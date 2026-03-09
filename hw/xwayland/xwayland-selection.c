/*
 * Copyright © 2026 Red Hat.
 *
 * Permission to use, copy, modify, distribute, and sell this software
 * and its documentation for any purpose is hereby granted without
 * fee, provided that the above copyright notice appear in all copies
 * and that both that copyright notice and this permission notice
 * appear in supporting documentation, and that the name of the
 * copyright holders not be used in advertising or publicity
 * pertaining to distribution of the software without specific,
 * written prior permission.  The copyright holders make no
 * representations about the suitability of this software for any
 * purpose.  It is provided "as is" without express or implied
 * warranty.
 *
 * THE COPYRIGHT HOLDERS DISCLAIM ALL WARRANTIES WITH REGARD TO THIS
 * SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
 * FITNESS, IN NO EVENT SHALL THE COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * SPECIAL, INDIRECT OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN
 * AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING
 * OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS
 * SOFTWARE.
 */

#ifdef HAVE_CONFIG_H
#include <xwayland-config.h>
#endif

#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <errno.h>

#include <X11/Xatom.h>

#include "xwayland-screen.h"
#include "xwayland-input.h"

#include "selection.h"
#include "windowstr.h"
#include "scrnintstr.h"
#include "os.h"
#include "os/osdep.h"

#include "primary-selection-unstable-v1-client-protocol.h"

#define TEXT_PLAIN_MIME "text/plain;charset=utf-8"
#define TEXT_PLAIN_LEGACY "text/plain"
#define MAX_OFFER_MIME_TYPES 32

/* write_all_to_fd: max ms of EAGAIN busy-retry without a successful write() */
#define WRITE_STALL_MS 1000

/* Couple of macros aimed at DebugF() essentially */
#define ATOM_NAME_HELPER(atom) (NameForAtom(atom) ? NameForAtom(atom) : "(?)")
#define STR_HELPER(s) ((s) ? (s) : "(null)")

struct mime_data_entry {
    struct xorg_list link;
    char *mime_type;
    char *data;
    size_t size;
};

struct xwl_selection_attrs {
    /* Wayland to X11: blobs read from Wayland offer, one per MIME type */
    struct xorg_list wl_mime_data;

    /* MIME reads in flight Wayland to X11 */
    struct xorg_list active_mime_reads;

    /* Acquisition time for ICCCM timestamp */
    CARD32 timestamp;

    /* Timestamp from the real X11 owner */
    TimeStamp x11_owner_time;

     /* MIME types collected from current Wayland offer */
    char *offer_mimes[MAX_OFFER_MIME_TYPES];
    int offer_mime_count;

    /* X11 to Wayland: MIME/atom pairs discovered via TARGETS query */
    char *x11_mimes[MAX_OFFER_MIME_TYPES];
    Atom x11_targets[MAX_OFFER_MIME_TYPES];
    int x11_mime_count;

    /* X11 to Wayland: queued send-data requests (lazy fetch) */
    struct xorg_list send_queue;
    Bool send_in_progress;
    Bool targets_pending;

    /* Generation counter: bumped on each new X11 to Wayland cycle
     * to detect and discard stale TARGETS / data replies.
     */
    uint32_t x11_serial;
    uint32_t targets_serial;

    uint32_t read_serial;
    Bool read_in_progress;
};

struct mime_read_slot {
    char *mime_type;
    char *data;
    size_t size;
};

struct mime_read_batch {
    struct xwl_selection *xwl_selection;
    struct xwl_selection_attrs *attrs;
    Atom selection_atom;
    uint32_t serial;
    int pending;
    int count;
    struct mime_read_slot *slots;
};

struct mime_part_closure {
    struct xorg_list link;
    struct mime_read_batch *batch;
    int index;
    int fd;
    char *data;
    size_t size;
};

static void xwl_selection_attrs_abort_mime_reads(struct xwl_selection_attrs *attrs);

struct x11_send_request {
    struct xorg_list link;
    int fd;
    Atom target;
    uint32_t serial;
};

struct xwl_selection {
    struct xwl_screen *xwl_screen;
    WindowPtr bridge_window;

    /* X11 atoms */
    Atom atom_primary;
    Atom atom_clipboard;
    Atom atom_utf8_string;
    Atom atom_text_plain;
    Atom atom_compound_text;
    Atom atom_targets;
    Atom atom_timestamp;
    Atom atom_wayland_clipboard;
    Atom atom_wayland_primary;
    Atom atom_clipboard_targets;
    Atom atom_primary_targets;
    Atom atom_incr;

    /* Wayland clipboard */
    struct wl_data_device_manager *data_device_manager;
    struct wl_data_device *data_device;
    struct wl_data_offer *clipboard_offer;
    struct wl_data_source *clipboard_source;

    /* Wayland primary selection */
    struct zwp_primary_selection_device_manager_v1 *primary_selection_manager;
    struct zwp_primary_selection_device_v1 *primary_selection_device;
    struct zwp_primary_selection_offer_v1 *primary_offer;
    struct zwp_primary_selection_source_v1 *primary_source;

    struct xwl_selection_attrs clipboard;
    struct xwl_selection_attrs primary;

    /* Serial to use for set_selection: captured when X11 app
     * claimed selection (selection_callback)
     */
    uint32_t set_selection_serial;

    Bool initialized;
};

static Bool
str_equals(const char *s1, const char *s2)
{
    if (s1 && s2)
        return strcmp(s1, s2) == 0;

    return s1 == s2;
}

static Atom
make_atom(const char *name)
{
    if (!name)
        return None;

    return MakeAtom(name, strlen(name), TRUE);
}

static Bool
mime_type_is_text(const char *mime_type)
{
    if (!mime_type)
        return FALSE;

    return strncmp(mime_type, "text/", 5) == 0;
}

/* Largest format-8 payload that still fits in one ChangeProperty big request */
static size_t
get_max_property_payload(void)
{
    static size_t max_property_payload = 0; /* cache value */
    uint64_t cap;
    uint64_t hdr;

    if (max_property_payload > 0)
        goto out;

    cap = (uint64_t) maxBigRequestSize << 2;
    hdr = (uint64_t) sz_xChangePropertyReq;
    assert (cap > hdr);

    max_property_payload = (size_t) (cap - hdr);

out:
    return max_property_payload;
}

static Bool
write_stalled(Time *last_ms)
{
    Time now = GetTimeInMillis();
    INT32 elapsed = (INT32) (now - *last_ms);

    if (elapsed < 0) {
        *last_ms = now;
        return FALSE;
    }

    return (CARD32) elapsed >= WRITE_STALL_MS;
}

static void
write_all_to_fd(int fd, const char *buf, size_t size)
{
    Time last_ms = GetTimeInMillis();

    while (size > 0) {
        ssize_t n = write(fd, buf, size);

        if (n > 0) {
            last_ms = GetTimeInMillis();
            DebugF("XWAYLAND: %s() - wrote %ld out of %lu bytes to fd %d\n",
                __FUNCTION__, (long) n, (unsigned long) size, fd);
            buf += (size_t) n;
            size -= (size_t) n;
        } else if (n == 0) {
            DebugF("XWAYLAND: %s() - write returned 0 on fd %d, %lu bytes left\n",
                   __FUNCTION__, fd, (unsigned long) size);
            break;
        } else if (n < 0 && errno == EINTR) {
            continue;
        } else if (n < 0 && ETEST(errno)) {
            if (write_stalled(&last_ms)) {
                DebugF("XWAYLAND: %s() - Write stalled on fd %d for >= %u ms, %lu bytes left\n",
                       __FUNCTION__, fd, WRITE_STALL_MS, (unsigned long) size);
                break;
            }
            continue;
        } else {
            DebugF("XWAYLAND: %s() - error %d (%s) writing to fd %d, aborting!\n",
                __FUNCTION__, errno, strerror(errno), fd);
            break;
        }
    }
}

static void
mime_data_list_clear(struct xorg_list *head)
{
    struct mime_data_entry *entry, *tmp;

    xorg_list_for_each_entry_safe(entry, tmp, head, link) {
        xorg_list_del(&entry->link);
        free(entry->mime_type);
        free(entry->data);
        free(entry);
    }
}

static struct mime_data_entry *
mime_data_list_find_by_atom(struct xorg_list *head, Atom target)
{
    struct mime_data_entry *entry;

    xorg_list_for_each_entry(entry, head, link) {
        if (make_atom(entry->mime_type) == target)
            return entry;
    }

    return NULL;
}

static struct mime_data_entry *
mime_data_list_find_text(struct xorg_list *head)
{
    struct mime_data_entry *entry;

    xorg_list_for_each_entry(entry, head, link) {
        if (mime_type_is_text(entry->mime_type) &&
            entry->data && entry->size > 0)
            return entry;
    }

    return NULL;
}

static void
offer_mimes_clear(struct xwl_selection_attrs *attrs)
{
    int i;

    for (i = 0; i < attrs->offer_mime_count; i++)
        free(attrs->offer_mimes[i]);

    attrs->offer_mime_count = 0;
}

static void
offer_mimes_append(struct xwl_selection_attrs *attrs, const char *mime_type)
{
    if (!mime_type)
        return;

    if (attrs->offer_mime_count >= MAX_OFFER_MIME_TYPES) {
        DebugF("XWAYLAND: %s() - MIME type limit reached (%d), ignoring \"%s\"\n",
               __FUNCTION__, MAX_OFFER_MIME_TYPES, mime_type);
        return;
    }

    attrs->offer_mimes[attrs->offer_mime_count] = XNFstrdup(mime_type);
    attrs->offer_mime_count++;
}

static void
x11_mimes_clear(struct xwl_selection_attrs *attrs)
{
    int i;

    for (i = 0; i < attrs->x11_mime_count; i++)
        free(attrs->x11_mimes[i]);

    attrs->x11_mime_count = 0;
}

static Bool
x11_mimes_contains(struct xwl_selection_attrs *attrs, const char *mime)
{
    int i;

    for (i = 0; i < attrs->x11_mime_count; i++) {
        if (str_equals(attrs->x11_mimes[i], mime))
            return TRUE;
    }

    return FALSE;
}

static void
x11_mimes_add(struct xwl_selection_attrs *attrs, const char *mime, Atom target)
{
    if (attrs->x11_mime_count >= MAX_OFFER_MIME_TYPES) {
        DebugF("XWAYLAND: %s() - X11 MIME type limit reached (%d), ignoring \"%s\"\n",
               __FUNCTION__, MAX_OFFER_MIME_TYPES, STR_HELPER(mime));
        return;
    }

    if (x11_mimes_contains(attrs, mime))
        return;

    attrs->x11_mimes[attrs->x11_mime_count] = XNFstrdup(mime);

    attrs->x11_targets[attrs->x11_mime_count] = target;
    attrs->x11_mime_count++;
}

static Atom
x11_mimes_find_target(struct xwl_selection_attrs *attrs, const char *mime)
{
    int i;

    for (i = 0; i < attrs->x11_mime_count; i++) {
        if (str_equals(attrs->x11_mimes[i], mime))
            return attrs->x11_targets[i];
    }

    return None;
}

static void
x11_send_queue_clear(struct xwl_selection_attrs *attrs)
{
    struct x11_send_request *req, *tmp;

    xorg_list_for_each_entry_safe(req, tmp, &attrs->send_queue, link) {
        xorg_list_del(&req->link);
        close(req->fd);
        free(req);
    }

    attrs->send_in_progress = FALSE;
}

static void
x11_send_enqueue(struct xwl_selection_attrs *attrs, int fd, Atom target)
{
    struct x11_send_request *req;

    req = XNFcallocarray(1, sizeof(*req));

    req->fd = fd;
    req->target = target;
    req->serial = attrs->x11_serial;

    xorg_list_append(&req->link, &attrs->send_queue);
}

static struct x11_send_request *
x11_send_dequeue(struct xwl_selection_attrs *attrs)
{
    struct x11_send_request *req;

    if (xorg_list_is_empty(&attrs->send_queue))
        return NULL;

    req = xorg_list_first_entry(&attrs->send_queue,
                                struct x11_send_request, link);
    xorg_list_del(&req->link);

    return req;
}

static void
x11_deliver_selection_req(Atom selection, Atom target, Window requestor,
                          Atom property, TimeStamp time)
{
    Selection *pSel;
    xEvent event;
    int rc;

    rc = dixLookupSelection(&pSel, selection, serverClient, DixReadAccess);
    if (rc != Success)
        return;

    if (pSel->window == None)
        return;

    if (pSel->client == serverClient)
        return;

    if (pSel->client && pSel->client->clientGone)
        return;

    memset(&event, 0, sizeof(xEvent));
    event.u.u.type = SelectionRequest;
    event.u.selectionRequest.owner = pSel->window;
    event.u.selectionRequest.time = time.milliseconds;
    event.u.selectionRequest.requestor = requestor;
    event.u.selectionRequest.selection = selection;
    event.u.selectionRequest.target = target;
    event.u.selectionRequest.property = property;

    WriteEventsToClient(pSel->client, 1, &event);
}

static void
xwl_selection_attrs_init(struct xwl_selection_attrs *attrs)
{
    xorg_list_init(&attrs->wl_mime_data);
    xorg_list_init(&attrs->send_queue);
    xorg_list_init(&attrs->active_mime_reads);
}

static void
xwl_selection_attrs_clear(struct xwl_selection_attrs *attrs)
{
    xwl_selection_attrs_abort_mime_reads(attrs);

    mime_data_list_clear(&attrs->wl_mime_data);
    offer_mimes_clear(attrs);
    x11_mimes_clear(attrs);
    x11_send_queue_clear(attrs);
    attrs->targets_pending = FALSE;
}

static void
xwl_selection_set_owner(struct xwl_selection *xwl_selection,
                        Atom selection_atom, Window window, TimeStamp time)
{
    if (window != None && !xwl_selection->bridge_window)
        return;

    dixSetSelectionOwner(serverClient, selection_atom, window, time);
}

static void
xwl_selection_maybe_clear_x11_owner(struct xwl_selection *xwl_selection,
                                    Atom selection_atom)
{
    Selection *pSel;

    if (dixLookupSelection(&pSel, selection_atom, serverClient, DixReadAccess) != Success)
        return;

    if (pSel->client != serverClient)
        return;

    UpdateCurrentTime();
    xwl_selection_set_owner(xwl_selection, selection_atom, None, currentTime);
}

static void
xwl_selection_set_bridge_as_owner(struct xwl_selection *xwl_selection,
                                  Atom selection_atom)
{
    UpdateCurrentTime();
    xwl_selection_set_owner(xwl_selection, selection_atom,
                            xwl_selection->bridge_window->drawable.id,
                            currentTime);
}

static void
xwl_selection_send_notify(ClientPtr requestor, Window requestor_win,
                          Atom selection, Atom target, Atom property,
                          TimeStamp time)
{
    xEvent event;

    memset(&event, 0, sizeof(event));
    event.u.u.type = SelectionNotify;
    event.u.selectionNotify.time = time.milliseconds;
    event.u.selectionNotify.requestor = requestor_win;
    event.u.selectionNotify.selection = selection;
    event.u.selectionNotify.target = target;
    event.u.selectionNotify.property = property;

    WriteEventsToClient(requestor, 1, &event);
}

static struct xwl_selection_attrs *
bridge_get_attrs(struct xwl_selection *xwl_selection, Atom selection)
{
    if (selection == xwl_selection->atom_primary)
        return &xwl_selection->primary;

    return &xwl_selection->clipboard;
}

static Bool
bridge_get_text(struct xwl_selection_attrs *attrs,
                const char **out_data, size_t *out_size)
{
    struct mime_data_entry *entry;

    entry = mime_data_list_find_text(&attrs->wl_mime_data);
    if (!entry)
        return FALSE;

    *out_data = entry->data;
    *out_size = entry->size;

    return TRUE;
}

static void
bridge_reply_targets(struct xwl_selection *xwl_selection,
                     ClientPtr requestor, Window requestor_win,
                     WindowPtr pRequestorWin,
                     Atom selection, Atom property, TimeStamp time,
                     struct xwl_selection_attrs *attrs)
{
    struct mime_data_entry *entry;
    Atom targets[MAX_OFFER_MIME_TYPES + 8];
    const char *text_data;
    size_t text_size;
    int n = 0;

    targets[n++] = xwl_selection->atom_targets;
    targets[n++] = xwl_selection->atom_timestamp;

    xorg_list_for_each_entry(entry, &attrs->wl_mime_data, link) {
        if (n >= MAX_OFFER_MIME_TYPES + 2)
            break;
        if (entry->data && entry->size > 0)
            targets[n++] = make_atom(entry->mime_type);
    }

    if (bridge_get_text(attrs, &text_data, &text_size)) {
        targets[n++] = xwl_selection->atom_utf8_string;
        targets[n++] = xwl_selection->atom_compound_text;
        targets[n++] = XA_STRING;
        targets[n++] = xwl_selection->atom_text_plain;
    }

    DebugF("XWAYLAND: %s() - publishing %d TARGETS atoms\n", __FUNCTION__, n);

    dixChangeWindowProperty(serverClient, pRequestorWin, property,
                            XA_ATOM, 32, PropModeReplace,
                            n, targets, FALSE);

    xwl_selection_send_notify(requestor, requestor_win, selection,
                              xwl_selection->atom_targets, property, time);
}

static void
bridge_reply_timestamp(struct xwl_selection *xwl_selection,
                       ClientPtr requestor, Window requestor_win,
                       WindowPtr pRequestorWin,
                       Atom selection, Atom property, TimeStamp time,
                       struct xwl_selection_attrs *attrs)
{
    dixChangeWindowProperty(serverClient, pRequestorWin, property,
                            XA_INTEGER, 32, PropModeReplace,
                            1, &attrs->timestamp, FALSE);

    xwl_selection_send_notify(requestor, requestor_win, selection,
                              xwl_selection->atom_timestamp, property, time);
}

static Bool
bridge_reply_mime_data(struct xwl_selection *xwl_selection,
                      ClientPtr requestor, Window requestor_win,
                      WindowPtr pRequestorWin,
                      Atom selection, Atom target, Atom property,
                      TimeStamp time, struct xwl_selection_attrs *attrs)
{
    struct mime_data_entry *entry;
    size_t max_payload = get_max_property_payload();
    int rc = 0;

    entry = mime_data_list_find_by_atom(&attrs->wl_mime_data, target);
    if (!entry || !entry->data || entry->size == 0)
        return FALSE;

    DebugF("XWAYLAND: %s() - target=%s size=%lu (max=%lu)\n",
           __FUNCTION__, ATOM_NAME_HELPER(target), (unsigned long) entry->size, (unsigned long) max_payload);

    if (entry->size > max_payload)
        goto fail;

    rc = dixChangeWindowProperty(serverClient, pRequestorWin, property,
                                 target, 8, PropModeReplace,
                                 entry->size, entry->data,
                                 FALSE);
    if (rc != Success)
        goto fail;

    xwl_selection_send_notify(requestor, requestor_win, selection,
                              target, property, time);

    return TRUE;

fail:
    ErrorF("XWAYLAND: bridge MIME data failed: code=%i, size=%lu, max payload=%lu\n",
           rc, (unsigned long) entry->size, (unsigned long) max_payload);
    DDXRingBell(0, 0, 0);

    return FALSE;
}

static Bool
bridge_reply_text(struct xwl_selection *xwl_selection,
                  ClientPtr requestor, Window requestor_win,
                  WindowPtr pRequestorWin,
                  Atom selection, Atom target, Atom property,
                  TimeStamp time, struct xwl_selection_attrs *attrs)
{
    const char *data;
    size_t size;
    size_t max_payload = get_max_property_payload();
    Atom reply_type = target;
    int rc = 0;

    if (!bridge_get_text(attrs, &data, &size))
        return FALSE;

    /* ICCCM: TEXT to reply with actual encoding (COMPOUND_TEXT for us) */
    if (target == xwl_selection->atom_text_plain)
        reply_type = xwl_selection->atom_compound_text;

    DebugF("XWAYLAND: %s() - reply_type=%s size=%lu (max=%lu)\n",
           __FUNCTION__, ATOM_NAME_HELPER(reply_type), (unsigned long) size, (unsigned long) max_payload);

    if (size > max_payload)
        goto fail;

    rc = dixChangeWindowProperty(serverClient, pRequestorWin, property,
                                 reply_type, 8, PropModeReplace,
                                 size, (void *) data, FALSE);
    if (rc != Success)
        goto fail;

    xwl_selection_send_notify(requestor, requestor_win, selection,
                              target, property, time);

    return TRUE;

fail:
    ErrorF("XWAYLAND: bridge MIME data failed: code=%i, size=%lu, max payload=%lu\n",
           rc, (unsigned long) size, (unsigned long) max_payload);
    DDXRingBell(0, 0, 0);

    return FALSE;
}

static Bool
is_text_target(struct xwl_selection *xwl_selection, Atom target)
{
    if (target == xwl_selection->atom_utf8_string)
        return TRUE;

    if (target == xwl_selection->atom_compound_text)
        return TRUE;

    if (target == xwl_selection->atom_text_plain)
        return TRUE;

    if (target == XA_STRING)
        return TRUE;

    return FALSE;
}

static void
xwl_selection_bridge_request(ScreenPtr screen, ClientPtr requestor,
                             Window requestor_win, Atom selection,
                             Atom target, Atom property, TimeStamp time)
{
    struct xwl_screen *xwl_screen = xwl_screen_get(screen);
    struct xwl_selection *xwl_selection;
    struct xwl_selection_attrs *attrs;
    WindowPtr pRequestorWin;
    int rc;

    if (!xwl_screen->selection_bridge) {
        ErrorF("XWAYLAND: bridge request: no selection_bridge!\n");
        return;
    }

    rc = dixLookupWindow(&pRequestorWin, requestor_win, requestor, DixSetAttrAccess);
    if (rc != Success) {
        ErrorF("XWAYLAND: bridge request: dixLookupWindow failed!\n");
        return;
    }

    xwl_selection = xwl_screen->selection_bridge;

    /* ICCCM: if property is None, use target as the property */
    if (property == None)
        property = target;

    attrs = bridge_get_attrs(xwl_selection, selection);

    DebugF("XWAYLAND: %s() - selection=%s target=%s property=%s requestor=0x%lx\n",
           __FUNCTION__, ATOM_NAME_HELPER(selection), ATOM_NAME_HELPER(target), ATOM_NAME_HELPER(property),
           (unsigned long) requestor_win);

    if (target == xwl_selection->atom_incr) {
        ErrorF("XWAYLAND: X11 client requested INCR transfer; not supported.\n");
        xwl_selection_send_notify(requestor, requestor_win, selection, target, None, time);
        DDXRingBell(0, 0, 0);

        return;
    }

    if (target == xwl_selection->atom_targets) {
        bridge_reply_targets(xwl_selection, requestor, requestor_win,
                             pRequestorWin, selection, property, time,
                             attrs);
        return;
    }

    if (target == xwl_selection->atom_timestamp) {
        bridge_reply_timestamp(xwl_selection, requestor, requestor_win,
                               pRequestorWin, selection, property, time,
                               attrs);
        return;
    }

    if (bridge_reply_mime_data(xwl_selection, requestor, requestor_win,
                              pRequestorWin, selection, target, property,
                              time, attrs)) {
        return;
    }

    if (is_text_target(xwl_selection, target)) {
        if (bridge_reply_text(xwl_selection, requestor, requestor_win,
                              pRequestorWin, selection, target, property,
                              time, attrs))
            return;
    }

    xwl_selection_send_notify(requestor, requestor_win, selection, target,
                              None, time);
}

static void
selection_bridge_request_callback(CallbackListPtr *pcbl, void *closure,
                                  void *data)
{
    struct xwl_screen *xwl_screen = closure;
    SelectionBridgeInfoRec *info = data;

    if (info->screen != xwl_screen->screen)
        return;

    xwl_selection_bridge_request(info->screen, info->client, info->requestor,
                                 info->selection, info->target, info->property,
                                 info->time);
}

static void
mime_read_batch_destroy(struct mime_read_batch *batch)
{
    int i;

    if (!batch)
        return;

    for (i = 0; i < batch->count; i++) {
        free(batch->slots[i].mime_type);
        free(batch->slots[i].data);
    }

    free(batch->slots);
    free(batch);
}

static void
xwl_selection_attrs_abort_mime_reads(struct xwl_selection_attrs *attrs)
{
    struct mime_part_closure *part, *tmp;

    xorg_list_for_each_entry_safe(part, tmp, &attrs->active_mime_reads, link) {
        struct mime_read_batch *batch = part->batch;

        SetNotifyFd(part->fd, NULL, 0, NULL);
        close(part->fd);
        xorg_list_del(&part->link);
        free(part->data);
        free(part);

        batch->pending--;
        if (batch->pending == 0)
            mime_read_batch_destroy(batch);
    }

    attrs->read_in_progress = FALSE;
}

static void
mime_batch_commit(struct mime_read_batch *batch)
{
    struct xwl_selection *xwl_selection = batch->xwl_selection;
    struct xwl_selection_attrs *attrs = batch->attrs;
    int i;
    Bool have_data = FALSE;

    if (batch->serial != attrs->read_serial) {
        DebugF("XWAYLAND: %s() - stale serial %u (current %u), discarding batch\n",
               __FUNCTION__, batch->serial, attrs->read_serial);
        goto out;
    }

    attrs->read_in_progress = FALSE;

    mime_data_list_clear(&attrs->wl_mime_data);

    for (i = 0; i < batch->count; i++) {
        struct mime_data_entry *entry;

        if (!batch->slots[i].data || batch->slots[i].size == 0) {
            DebugF("XWAYLAND: %s() - slot %d MIME=\"%s\" is empty\n",
                   __FUNCTION__, i, STR_HELPER(batch->slots[i].mime_type));
            continue;
        }

        entry = XNFcallocarray(1, sizeof(struct mime_data_entry));
        entry->mime_type = batch->slots[i].mime_type;
        entry->data = batch->slots[i].data;
        entry->size = batch->slots[i].size;

        batch->slots[i].mime_type = NULL;
        batch->slots[i].data = NULL;

        xorg_list_append(&entry->link, &attrs->wl_mime_data);
        have_data = TRUE;
        DebugF("XWAYLAND: %s() - slot %d MIME=\"%s\" size=%lu bytes\n",
               __FUNCTION__, i, STR_HELPER(entry->mime_type), (unsigned long) entry->size);
    }

    if (!have_data) {
        DebugF("XWAYLAND: %s() - no data in any MIME slots!\n", __FUNCTION__);
        goto out;
    }

    UpdateCurrentTime();
    attrs->timestamp = currentTime.milliseconds;
    xwl_selection_set_bridge_as_owner(xwl_selection, batch->selection_atom);

out:
    mime_read_batch_destroy(batch);
}

static void
mime_part_read_handler(int fd, int ready, void *closure_data)
{
    struct mime_part_closure *part = closure_data;
    struct mime_read_batch *batch = part->batch;
    size_t max_payload = get_max_property_payload();
    char buf[4096];
    ssize_t n;

    (void) ready;

    for (;;) {
        n = read(fd, buf, sizeof(buf));
        if (n > 0) {
            size_t space = max_payload > part->size ? max_payload - part->size : 0;
            size_t to_copy = (size_t) n <= space ? (size_t) n : space;

            if (to_copy > 0) {
                part->data = XNFrealloc(part->data,
                                        (unsigned long) (part->size + to_copy));
                memcpy(part->data + part->size, buf, to_copy);
                part->size += to_copy;
            }

            if (part->size >= max_payload || (size_t) n > space) {
                DebugF("XWAYLAND: %s() - limit reached after %lu bytes for slot %d from fd %d.\n",
                       __FUNCTION__, (unsigned long) part->size, part->index, fd);
                break;
            }
        } else if (n == 0) {
            DebugF("XWAYLAND: %s() - read %lu bytes for slot %d from fd %d\n",
                   __FUNCTION__, (unsigned long) part->size, part->index, fd);
            break;
        } else if (errno == EINTR) {
            continue;
        } else if (ETEST(errno)) {
            return;
        } else {
            DebugF("XWAYLAND: %s() - error %d (%s) on slot %d reading from fd %d after reading %lu bytes\n",
                __FUNCTION__, errno, strerror(errno), part->index, fd, (unsigned long) part->size);
            break;
        }
    }

    xorg_list_del(&part->link);
    SetNotifyFd(part->fd, NULL, 0, NULL);
    close(part->fd);

    batch->slots[part->index].data = part->data;
    batch->slots[part->index].size = part->size;
    part->data = NULL;
    free(part);

    batch->pending--;
    if (batch->pending == 0)
        mime_batch_commit(batch);
}

static void
offer_receive_for_mime(struct xwl_selection *xwl_selection,
                       void *offer, Atom selection_atom,
                       const char *mime_type, int fd)
{
    if (selection_atom == xwl_selection->atom_primary)
        zwp_primary_selection_offer_v1_receive(offer, mime_type, fd);
    else
        wl_data_offer_receive(offer, mime_type, fd);
}

static void
start_offer_read(struct xwl_selection *xwl_selection,
                 struct xwl_selection_attrs *attrs,
                 void *offer, Atom selection_atom)
{
    struct mime_read_batch *batch;
    int i;

    if (attrs->offer_mime_count == 0)
        return;

    if (attrs->read_in_progress)
        attrs->read_serial++;

    batch = XNFcallocarray(1, sizeof(struct mime_read_batch));
    batch->count = attrs->offer_mime_count;
    batch->slots = XNFcallocarray(batch->count, sizeof(struct mime_read_slot));
    batch->xwl_selection = xwl_selection;
    batch->attrs = attrs;
    batch->selection_atom = selection_atom;
    batch->serial = ++attrs->read_serial;

    DebugF("XWAYLAND: %s() - %d MIME types, batch serial %u selection=%s\n",
           __FUNCTION__, batch->count, batch->serial, ATOM_NAME_HELPER(selection_atom));

    for (i = 0; i < batch->count; i++) {
        struct mime_part_closure *part;
        int pipe_fds[2];

        batch->slots[i].mime_type = XNFstrdup(attrs->offer_mimes[i]);

        if (pipe(pipe_fds) != 0)
            continue;

        if (fcntl(pipe_fds[0], F_SETFL,
                  fcntl(pipe_fds[0], F_GETFL) | O_NONBLOCK) < 0) {
            close(pipe_fds[0]);
            close(pipe_fds[1]);
            continue;
        }

        offer_receive_for_mime(xwl_selection, offer, selection_atom,
                               attrs->offer_mimes[i], pipe_fds[1]);
        close(pipe_fds[1]);

        part = XNFcallocarray(1, sizeof(*part));

        part->batch = batch;
        part->index = i;
        part->fd = pipe_fds[0];
        xorg_list_append(&part->link, &attrs->active_mime_reads);
        batch->pending++;

        if (!SetNotifyFd(part->fd, mime_part_read_handler, X_NOTIFY_READ, part)) {
            xorg_list_del(&part->link);
            batch->pending--;
            close(part->fd);
            free(part);
            continue;
        }
    }

    wl_display_flush(xwl_selection->xwl_screen->display);

    if (batch->pending == 0) {
        mime_read_batch_destroy(batch);
        return;
    }

    attrs->read_in_progress = TRUE;
}

static void
xwl_data_offer(void *data, struct wl_data_offer *offer,
               const char *mime_type)
{
    struct xwl_selection *xwl_selection = data;

    offer_mimes_append(&xwl_selection->clipboard, mime_type);
}

static const struct wl_data_offer_listener data_offer_listener = {
    .offer = xwl_data_offer,
};

static void
xwl_primary_offer(void *data,
                  struct zwp_primary_selection_offer_v1 *offer,
                  const char *mime_type)
{
    struct xwl_selection *xwl_selection = data;

    offer_mimes_append(&xwl_selection->primary, mime_type);
}

static const struct zwp_primary_selection_offer_v1_listener
    primary_offer_listener = {
    .offer = xwl_primary_offer,
};

static void
data_device_data_offer(void *data,
                       struct wl_data_device *device,
                       struct wl_data_offer *offer)
{
    struct xwl_selection *xwl_selection = data;

    if (xwl_selection->clipboard_offer)
        wl_data_offer_destroy(xwl_selection->clipboard_offer);

    xwl_selection->clipboard_offer = offer;
    offer_mimes_clear(&xwl_selection->clipboard);

    if (offer)
        wl_data_offer_add_listener(offer, &data_offer_listener,
                                   xwl_selection);
}

static void
data_device_selection(void *data,
                      struct wl_data_device *device,
                      struct wl_data_offer *offer)
{
    struct xwl_selection *xwl_selection = data;

    if (xwl_selection->clipboard_offer &&
        xwl_selection->clipboard_offer != offer) {
        wl_data_offer_destroy(xwl_selection->clipboard_offer);
    }

    xwl_selection->clipboard_offer = offer;

    if (offer && !xwl_selection->clipboard_source)
        start_offer_read(xwl_selection, &xwl_selection->clipboard,
                         offer, xwl_selection->atom_clipboard);

    if (!xwl_selection->clipboard.read_in_progress)
        xwl_selection_maybe_clear_x11_owner(xwl_selection,
                                            xwl_selection->atom_clipboard);
}

static void
data_device_enter(void *data, struct wl_data_device *device,
                  uint32_t serial, struct wl_surface *surface,
                  wl_fixed_t x, wl_fixed_t y, struct wl_data_offer *offer)
{
}

static void
data_device_leave(void *data, struct wl_data_device *device)
{
}

static void
data_device_motion(void *data, struct wl_data_device *device,
                   uint32_t time, wl_fixed_t x, wl_fixed_t y)
{
}

static void
data_device_drop(void *data, struct wl_data_device *device)
{
}

static const struct wl_data_device_listener data_device_listener = {
    .data_offer = data_device_data_offer,
    .enter = data_device_enter,
    .leave = data_device_leave,
    .motion = data_device_motion,
    .drop = data_device_drop,
    .selection = data_device_selection,
};

static void
primary_selection_device_data_offer(void *data,
                                    struct zwp_primary_selection_device_v1 *device,
                                    struct zwp_primary_selection_offer_v1 *offer)
{
    struct xwl_selection *xwl_selection = data;

    if (xwl_selection->primary_offer)
        zwp_primary_selection_offer_v1_destroy(xwl_selection->primary_offer);

    xwl_selection->primary_offer = offer;
    offer_mimes_clear(&xwl_selection->primary);

    if (offer)
        zwp_primary_selection_offer_v1_add_listener(offer,
                                                    &primary_offer_listener,
                                                    xwl_selection);
}

static void
primary_selection_selection(void *data,
                            struct zwp_primary_selection_device_v1 *device,
                            struct zwp_primary_selection_offer_v1 *offer)
{
    struct xwl_selection *xwl_selection = data;

    if (xwl_selection->primary_offer &&
        xwl_selection->primary_offer != offer) {
        zwp_primary_selection_offer_v1_destroy(xwl_selection->primary_offer);
    }

    xwl_selection->primary_offer = offer;

    if (offer && !xwl_selection->primary_source)
        start_offer_read(xwl_selection, &xwl_selection->primary,
                         offer, xwl_selection->atom_primary);

    if (!xwl_selection->primary.read_in_progress)
        xwl_selection_maybe_clear_x11_owner(xwl_selection,
                                            xwl_selection->atom_primary);
}

static const struct zwp_primary_selection_device_v1_listener
    primary_selection_device_listener = {
    .data_offer = primary_selection_device_data_offer,
    .selection = primary_selection_selection,
};

static Bool
should_skip_x11_atom(struct xwl_selection *xwl_selection, Atom atom)
{
    if (is_text_target(xwl_selection, atom))
        return TRUE;

    if (atom == xwl_selection->atom_targets)
        return TRUE;

    if (atom == xwl_selection->atom_timestamp)
        return TRUE;

    return FALSE;
}

static void
parse_targets_to_mimes(struct xwl_selection *xwl_selection,
                       struct xwl_selection_attrs *attrs,
                       Atom *atoms, int natoms)
{
    int i;

    x11_mimes_clear(attrs);

    for (i = 0; i < natoms; i++) {
        if (atoms[i] == xwl_selection->atom_utf8_string) {
            x11_mimes_add(attrs, TEXT_PLAIN_MIME, atoms[i]);
            x11_mimes_add(attrs, TEXT_PLAIN_LEGACY, atoms[i]);
        }
        else if (atoms[i] == XA_STRING) {
            x11_mimes_add(attrs, TEXT_PLAIN_LEGACY, atoms[i]);
        }
    }

    for (i = 0; i < natoms; i++) {
        const char *name;

        if (should_skip_x11_atom(xwl_selection, atoms[i]))
            continue;

        name = NameForAtom(atoms[i]);
        if (name && strchr(name, '/'))
            x11_mimes_add(attrs, name, atoms[i]);
    }
}

static void
x11_send_start_next(struct xwl_selection *xwl_selection,
                    struct xwl_selection_attrs *attrs,
                    Atom selection, Atom property)
{
    struct x11_send_request *req;

    if (attrs->send_in_progress)
        return;

    if (xorg_list_is_empty(&attrs->send_queue))
        return;

    req = xorg_list_first_entry(&attrs->send_queue,
                                struct x11_send_request, link);

    attrs->send_in_progress = TRUE;

    DebugF("XWAYLAND: %s() - selection=%s target=%s serial=%u\n",
           __FUNCTION__, ATOM_NAME_HELPER(selection), ATOM_NAME_HELPER(req->target), attrs->x11_serial);

    x11_deliver_selection_req(selection, req->target,
                              xwl_selection->bridge_window->drawable.id,
                              property, attrs->x11_owner_time);
}

static void
data_source_send(void *data, struct wl_data_source *source,
                 const char *mime_type, int32_t fd)
{
    struct xwl_selection *xwl_selection = data;
    struct xwl_selection_attrs *attrs = &xwl_selection->clipboard;
    Atom target;

    target = x11_mimes_find_target(attrs, mime_type);
    if (target == None) {
        DebugF("XWAYLAND: %s() - no X11 target for MIME=\"%s\", closing fd\n",
               __FUNCTION__, STR_HELPER(mime_type));
        close(fd);
        return;
    }

    DebugF("XWAYLAND: %s() - MIME=\"%s\" X11 target=%s fd=%d\n",
           __FUNCTION__, STR_HELPER(mime_type), ATOM_NAME_HELPER(target), fd);

    x11_send_enqueue(attrs, fd, target);
    x11_send_start_next(xwl_selection, attrs,
                        xwl_selection->atom_clipboard,
                        xwl_selection->atom_wayland_clipboard);
}

static void
data_source_cancelled(void *data, struct wl_data_source *source)
{
    struct xwl_selection *xwl_selection = data;

    wl_data_source_destroy(source);
    xwl_selection->clipboard_source = NULL;
    x11_send_queue_clear(&xwl_selection->clipboard);
    x11_mimes_clear(&xwl_selection->clipboard);
}

static const struct wl_data_source_listener data_source_listener = {
    .target = NULL,
    .send = data_source_send,
    .cancelled = data_source_cancelled,
};

static void
primary_source_send(void *data,
                    struct zwp_primary_selection_source_v1 *source,
                    const char *mime_type, int32_t fd)
{
    struct xwl_selection *xwl_selection = data;
    struct xwl_selection_attrs *attrs = &xwl_selection->primary;
    Atom target;

    target = x11_mimes_find_target(attrs, mime_type);
    if (target == None) {
        DebugF("XWAYLAND: %s() - no X11 target for MIME=\"%s\", closing fd\n",
               __FUNCTION__, STR_HELPER(mime_type));
        close(fd);
        return;
    }

    DebugF("XWAYLAND: %s() - MIME=\"%s\" X11 target=%s fd=%d\n",
           __FUNCTION__, STR_HELPER(mime_type), ATOM_NAME_HELPER(target), fd);

    x11_send_enqueue(attrs, fd, target);
    x11_send_start_next(xwl_selection, attrs,
                        xwl_selection->atom_primary,
                        xwl_selection->atom_wayland_primary);
}

static void
primary_source_cancelled(void *data,
                         struct zwp_primary_selection_source_v1 *source)
{
    struct xwl_selection *xwl_selection = data;

    zwp_primary_selection_source_v1_destroy(source);
    xwl_selection->primary_source = NULL;
    x11_send_queue_clear(&xwl_selection->primary);
    x11_mimes_clear(&xwl_selection->primary);
}

static const struct zwp_primary_selection_source_v1_listener
    primary_source_listener = {
    .send = primary_source_send,
    .cancelled = primary_source_cancelled,
};

static void
request_x11_targets(struct xwl_selection *xwl_selection,
                    Atom selection, Atom property, TimeStamp time)
{
    x11_deliver_selection_req(selection,
                              xwl_selection->atom_targets,
                              xwl_selection->bridge_window->drawable.id,
                              property, time);
}

static void
create_clipboard_source_from_targets(struct xwl_selection *xwl_selection)
{
    struct xwl_selection_attrs *attrs = &xwl_selection->clipboard;
    struct wl_data_source *data_source;
    int i;

    if (attrs->x11_mime_count == 0)
        return;

    if (xwl_selection->clipboard_source) {
        wl_data_source_destroy(xwl_selection->clipboard_source);
        xwl_selection->clipboard_source = NULL;
    }

    data_source = wl_data_device_manager_create_data_source(
        xwl_selection->data_device_manager);

    for (i = 0; i < attrs->x11_mime_count; i++)
        wl_data_source_offer(data_source, attrs->x11_mimes[i]);

    wl_data_source_add_listener(data_source, &data_source_listener,
                                xwl_selection);

    xwl_selection->clipboard_source = data_source;

    wl_data_device_set_selection(xwl_selection->data_device,
                                 data_source,
                                 xwl_selection->set_selection_serial);
}

static void
create_primary_source_from_targets(struct xwl_selection *xwl_selection)
{
    struct xwl_selection_attrs *attrs = &xwl_selection->primary;
    struct zwp_primary_selection_source_v1 *primary_source;
    int i;

    if (attrs->x11_mime_count == 0)
        return;

    if (xwl_selection->primary_source) {
        zwp_primary_selection_source_v1_destroy(xwl_selection->primary_source);
        xwl_selection->primary_source = NULL;
    }

    primary_source = zwp_primary_selection_device_manager_v1_create_source(xwl_selection->primary_selection_manager);

    for (i = 0; i < attrs->x11_mime_count; i++)
        zwp_primary_selection_source_v1_offer(primary_source,
                                              attrs->x11_mimes[i]);

    zwp_primary_selection_source_v1_add_listener(primary_source, &primary_source_listener, xwl_selection);

    xwl_selection->primary_source = primary_source;

    zwp_primary_selection_device_v1_set_selection(xwl_selection->primary_selection_device, primary_source, xwl_selection->set_selection_serial);
}

static void
selection_set_clipboard_source(struct xwl_selection *xwl_selection,
                               TimeStamp owner_time)
{
    struct xwl_selection_attrs *attrs = &xwl_selection->clipboard;

    attrs->x11_serial++;
    attrs->targets_serial = attrs->x11_serial;
    attrs->targets_pending = TRUE;
    attrs->x11_owner_time = owner_time;
    x11_send_queue_clear(attrs);
    x11_mimes_clear(attrs);

    request_x11_targets(xwl_selection,
                        xwl_selection->atom_clipboard,
                        xwl_selection->atom_clipboard_targets,
                        owner_time);
}

static void
selection_set_primary_source(struct xwl_selection *xwl_selection,
                             TimeStamp owner_time)
{
    struct xwl_selection_attrs *attrs = &xwl_selection->primary;

    if (!xwl_selection->primary_selection_device)
        return;

    attrs->x11_serial++;
    attrs->targets_serial = attrs->x11_serial;
    attrs->targets_pending = TRUE;
    attrs->x11_owner_time = owner_time;
    x11_send_queue_clear(attrs);
    x11_mimes_clear(attrs);

    request_x11_targets(xwl_selection,
                        xwl_selection->atom_primary,
                        xwl_selection->atom_primary_targets,
                        owner_time);
}

static void
selection_callback(CallbackListPtr *p, void *data, void *arg)
{
    struct xwl_screen *xwl_screen = data;
    SelectionInfoRec *info = arg;
    struct xwl_selection *xwl_selection;

    if (!xwl_screen->selection_bridge || info->kind != SelectionSetOwner)
        return;

    if (info->client == serverClient)
        return;

    xwl_selection = xwl_screen->selection_bridge;
    xwl_selection->set_selection_serial = xwl_screen->serial;

    if (info->selection->selection == xwl_selection->atom_clipboard) {
        selection_set_clipboard_source(xwl_selection,
                                       info->selection->lastTimeChanged);
    }
    else if (info->selection->selection == xwl_selection->atom_primary &&
             xwl_selection->primary_selection_device) {
        selection_set_primary_source(xwl_selection,
                                     info->selection->lastTimeChanged);
    }
}

static char *
latin1_to_utf8(const char *src, size_t src_len, size_t *out_len)
{
    size_t i, n = 0;
    char *utf8;

    for (i = 0; i < src_len; i++) {
        if ((unsigned char) src[i] < 0x80)
            n += 1;
        else
            n += 2;
    }

    utf8 = XNFalloc((unsigned long) (n + 1));

    n = 0;
    for (i = 0; i < src_len; i++) {
        unsigned char c = (unsigned char) src[i];

        if (c < 0x80) {
            utf8[n++] = (char) c;
        } else {
            utf8[n++] = (char) (0xC0 | (c >> 6));
            utf8[n++] = (char) (0x80 | (c & 0x3F));
        }
    }

    utf8[n] = '\0';
    *out_len = n;

    return utf8;
}

static void
handle_targets_reply(struct xwl_selection *xwl_selection,
                     struct xwl_selection_attrs *attrs,
                     PropertyPtr prop, Bool is_primary)
{
    Atom *atoms;
    int natoms;
    int i;

    attrs->targets_pending = FALSE;

    if (attrs->targets_serial != attrs->x11_serial)
        return;

    if (prop->type != XA_ATOM || prop->format != 32)
        return;

    if (prop->size == 0 || !prop->data)
        return;

    atoms = (Atom *) prop->data;
    natoms = (int) prop->size;

    for (i = 0; i < natoms; i++) {
        if (atoms[i] == xwl_selection->atom_incr) {
            ErrorF("XWAYLAND: X11 owner advertises INCR; not supported\n");
            break;
        }
    }

    parse_targets_to_mimes(xwl_selection, attrs, atoms, natoms);

    if (is_primary)
        create_primary_source_from_targets(xwl_selection);
    else
        create_clipboard_source_from_targets(xwl_selection);
}

static void
write_prop_data_to_fd(int fd, PropertyPtr prop, Atom target)
{
    const char *data;
    size_t size;
    char *converted = NULL;

    if (prop->size == 0 || !prop->data) {
        DebugF("XWAYLAND: %s() - empty property, closing fd\n", __FUNCTION__);
        close(fd);
        return;
    }

    data = (const char *) prop->data;
    size = (size_t) prop->size;

    if (target == XA_STRING) {
        converted = latin1_to_utf8(data, size, &size);
        data = converted;
    }

    DebugF("XWAYLAND: %s() - writing %lu bytes to Wayland (prop size=%u format=%d target=%s)\n",
           __FUNCTION__, (unsigned long) size, (unsigned) prop->size, (int) prop->format, ATOM_NAME_HELPER(target));
    write_all_to_fd(fd, data, size);
    free(converted);
    close(fd);
}

static void
handle_send_data_reply(struct xwl_selection *xwl_selection,
                       struct xwl_selection_attrs *attrs,
                       PropertyPtr prop, Atom selection, Atom property)
{
    struct x11_send_request *req;

    req = x11_send_dequeue(attrs);
    if (!req)
        return;

    if (req->serial != attrs->x11_serial) {
        close(req->fd);
        free(req);
        goto fail;
    }

    DebugF("XWAYLAND: %s() - type=%s size=%lu (format=%d) selection=%s\n",
           __FUNCTION__, ATOM_NAME_HELPER(prop->type), (unsigned long) prop->size, (int) prop->format, ATOM_NAME_HELPER(selection));

    if (prop->type == xwl_selection->atom_incr) {
        ErrorF("XWAYLAND: X11 owner uses INCR; not supported\n");
        close(req->fd);
        free(req);
        goto fail;
    }

    write_prop_data_to_fd(req->fd, prop, req->target);
    free(req);

    attrs->send_in_progress = FALSE;

    x11_send_start_next(xwl_selection, attrs, selection, property);

    return;

fail:
    attrs->send_in_progress = FALSE;
    x11_send_queue_clear(attrs);
    DDXRingBell(0, 0, 0);
}

static void
property_callback(CallbackListPtr *p, void *closure, void *calldata)
{
    PropertyStateRec *rec = calldata;
    struct xwl_screen *xwl_screen = closure;
    struct xwl_selection *xwl_selection;
    PropertyPtr prop;

    if (!xwl_screen->selection_bridge)
        return;

    xwl_selection = xwl_screen->selection_bridge;

    if (rec->win != xwl_selection->bridge_window)
        return;

    if (rec->state != PropertyNewValue)
        return;

    prop = rec->prop;

    DebugF("XWAYLAND: %s() - PropertyNewValue win=0x%lx prop=%s\n",
           __FUNCTION__, (unsigned long) rec->win->drawable.id, ATOM_NAME_HELPER(prop->propertyName));

    if (prop->propertyName == xwl_selection->atom_clipboard_targets &&
        xwl_selection->clipboard.targets_pending) {
        handle_targets_reply(xwl_selection, &xwl_selection->clipboard,
                             prop, FALSE);
        return;
    }

    if (prop->propertyName == xwl_selection->atom_primary_targets &&
        xwl_selection->primary.targets_pending) {
        handle_targets_reply(xwl_selection, &xwl_selection->primary,
                             prop, TRUE);
        return;
    }

    if (prop->propertyName == xwl_selection->atom_wayland_clipboard &&
        xwl_selection->clipboard_source) {
        handle_send_data_reply(xwl_selection, &xwl_selection->clipboard,
                               prop, xwl_selection->atom_clipboard,
                               xwl_selection->atom_wayland_clipboard);
        return;
    }

    if (prop->propertyName == xwl_selection->atom_wayland_primary &&
        xwl_selection->primary_source) {
        handle_send_data_reply(xwl_selection, &xwl_selection->primary,
                               prop, xwl_selection->atom_primary,
                               xwl_selection->atom_wayland_primary);
        return;
    }
}

static Bool
create_bridge_window(struct xwl_selection *xwl_selection)
{
    ScreenPtr screen = xwl_selection->xwl_screen->screen;
    WindowPtr pRoot = screen->root;
    WindowPtr pWin;
    int mask = CWEventMask;
    XID vlist[1];
    int error;
    Window wid;

    wid = FakeClientID(serverClient->index);
    vlist[0] = PropertyChangeMask;
    pWin = CreateWindow(wid, pRoot,
                        -100, -100, 1, 1, 0, InputOnly, mask, vlist,
                        0, serverClient, wVisual(pRoot), &error);

    if (pWin == NULL) {
        ErrorF("XWAYLAND: Failed to create bridge window: %d\n", error);
        return FALSE;
    }

    if (!AddResource(pWin->drawable.id, X11_RESTYPE_WINDOW, (void *) pWin)) {
        ErrorF("XWAYLAND: Failed to add resource for the bridge window\n");
        screen->DestroyWindow(pWin);
        return FALSE;
    }

    xwl_selection->bridge_window = pWin;

    return TRUE;
}

static void
xwl_selection_init_internal(struct xwl_screen *xwl_screen,
                            struct xwl_seat *xwl_seat)
{
    struct xwl_selection *xwl_selection;

    xwl_selection = XNFcallocarray(1, sizeof(struct xwl_selection));
    xwl_selection->xwl_screen = xwl_screen;
    xwl_screen->selection_bridge = xwl_selection;

    xwl_selection_attrs_init(&xwl_selection->clipboard);
    xwl_selection_attrs_init(&xwl_selection->primary);

    xwl_selection->atom_primary = make_atom("PRIMARY");
    xwl_selection->atom_clipboard = make_atom("CLIPBOARD");
    xwl_selection->atom_utf8_string = make_atom("UTF8_STRING");
    xwl_selection->atom_text_plain = make_atom("TEXT");
    xwl_selection->atom_compound_text = make_atom("COMPOUND_TEXT");
    xwl_selection->atom_targets = make_atom("TARGETS");
    xwl_selection->atom_timestamp = make_atom("TIMESTAMP");
    xwl_selection->atom_wayland_clipboard = make_atom("XWAYLAND_CLIPBOARD");
    xwl_selection->atom_wayland_primary =  make_atom("XWAYLAND_PRIMARY");
    xwl_selection->atom_clipboard_targets = make_atom("XWAYLAND_CLIPBOARD_TARGETS");
    xwl_selection->atom_primary_targets = make_atom("XWAYLAND_PRIMARY_TARGETS");
    xwl_selection->atom_incr = make_atom("INCR");

    xwl_selection->data_device_manager = xwl_screen->data_device_manager;
    xwl_selection->primary_selection_manager =
        xwl_screen->primary_selection_manager;

    if (!create_bridge_window(xwl_selection)) {
        free(xwl_selection);
        xwl_screen->selection_bridge = NULL;
        return;
    }

    xwl_selection->data_device = wl_data_device_manager_get_data_device(xwl_selection->data_device_manager, xwl_seat->seat);
    wl_data_device_add_listener(xwl_selection->data_device, &data_device_listener, xwl_selection);

    if (xwl_selection->primary_selection_manager) {
        xwl_selection->primary_selection_device =
            zwp_primary_selection_device_manager_v1_get_device(xwl_selection->primary_selection_manager,
                                                               xwl_seat->seat);
        zwp_primary_selection_device_v1_add_listener(xwl_selection->primary_selection_device,
                                                     &primary_selection_device_listener,
                                                     xwl_selection);
    }

    AddCallback(&SelectionBridgeCallback, selection_bridge_request_callback, xwl_screen);
    AddCallback(&SelectionCallback, selection_callback, xwl_screen);
    AddCallback(&PropertyStateCallback, property_callback, xwl_screen);

    xwl_selection->initialized = TRUE;
}

void
xwl_selection_init(struct xwl_seat *xwl_seat)
{
    struct xwl_screen *xwl_screen = xwl_seat->xwl_screen;

    if (xwl_screen->selection_bridge)
        return;

    if (!xwl_screen->data_device_manager)
        return;

    xwl_selection_init_internal(xwl_screen, xwl_seat);
}

void
xwl_selection_fini(struct xwl_seat *xwl_seat)
{
    struct xwl_screen *xwl_screen = xwl_seat->xwl_screen;
    struct xwl_selection *xwl_selection = xwl_screen->selection_bridge;

    if (!xwl_selection)
        return;

    DeleteCallback(&SelectionBridgeCallback, selection_bridge_request_callback, xwl_screen);
    DeleteCallback(&SelectionCallback, selection_callback, xwl_screen);
    DeleteCallback(&PropertyStateCallback, property_callback, xwl_screen);

    if (xwl_selection->clipboard_offer)
        wl_data_offer_destroy(xwl_selection->clipboard_offer);

    if (xwl_selection->clipboard_source)
        wl_data_source_destroy(xwl_selection->clipboard_source);

    if (xwl_selection->data_device)
        wl_data_device_destroy(xwl_selection->data_device);

    if (xwl_selection->primary_offer)
        zwp_primary_selection_offer_v1_destroy(xwl_selection->primary_offer);

    if (xwl_selection->primary_source)
        zwp_primary_selection_source_v1_destroy(xwl_selection->primary_source);

    if (xwl_selection->primary_selection_device)
        zwp_primary_selection_device_v1_destroy(xwl_selection->primary_selection_device);

    xwl_selection_attrs_clear(&xwl_selection->clipboard);
    xwl_selection_attrs_clear(&xwl_selection->primary);

    free(xwl_selection);
    xwl_screen->selection_bridge = NULL;
}
