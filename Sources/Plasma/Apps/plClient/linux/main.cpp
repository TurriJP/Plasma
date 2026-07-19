/*==LICENSE==*

CyanWorlds.com Engine - MMOG client, server and tools
Copyright (C) 2011  Cyan Worlds, Inc.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

Additional permissions under GNU GPL version 3 section 7

If you modify this Program, or any covered work, by linking or
combining it with any of RAD Game Tools Bink SDK, Autodesk 3ds Max SDK,
NVIDIA PhysX SDK, Microsoft DirectX SDK, OpenSSL library, Independent
JPEG Group JPEG library, Microsoft Windows Media SDK, or Apple QuickTime SDK
(or a modified version of those libraries),
containing parts covered by the terms of the Bink SDK EULA, 3ds Max EULA,
PhysX SDK EULA, DirectX SDK EULA, OpenSSL and SSLeay licenses, IJG
JPEG Library README, Windows Media SDK EULA, or QuickTime SDK EULA, the
licensors of this Program grant you additional
permission to convey the resulting work. Corresponding Source for a
non-source form of such a combination shall include the source code for
the parts of OpenSSL and IJG JPEG Library used as well as that of the covered
work.

You can contact Cyan Worlds, Inc. by email legal@cyan.com
 or by snail mail at:
      Cyan Worlds, Inc.
      14617 N Newport Hwy
      Mead, WA   99021

*==LICENSE==*/

#include <algorithm>
#include <cstring>
#include <unordered_set>
#include <string_theory/stdio>

#include <curl/curl.h>
#include <regex>
#include <termios.h>
#include <unistd.h>
#include <xcb/xcb.h>
#include <xcb/xcb_keysyms.h>
#include <xcb/xfixes.h>
#include <xcb/xproto.h>
#include <X11/Xlib-xcb.h>

// Undefine the problematic X11 stuff
#undef Status

#include "HeadSpin.h"
#include "plCmdParser.h"
#include "plPipeline.h"
#include "plProduct.h"
#include "pcSmallRect.h"
#include "hsStream.h"

#include "plClient.h"
#include "plClientLoader.h"

#include "pnEncryption/plChallengeHash.h"

#include "plInputCore/plInputManager.h"
#include "plMessage/plInputEventMsg.h"
#include "plMessageBox/hsMessageBox.h"
#include "plNetClient/plNetClientMgr.h"
#include "plNetGameLib/plNetGameLib.h"
#include "plPhysX/plPXSimulation.h"
#include "plPipeline/hsG3DDeviceSelector.h"
#include "plProgressMgr/plProgressMgr.h"
#include "plResMgr/plVersion.h"
#include "plStatusLog/plStatusLog.h"

#include "pfConsoleCore/pfConsoleEngine.h"
#include "pfConsoleCore/pfServerIni.h"
#include "pfPasswordStore/pfPasswordStore.h"

extern bool gDataServerLocal;
extern bool gPythonLocal;
extern bool gSDLLocal;

static plClientLoader gClient;
static Display* gDisplay;
static xcb_connection_t* gXConn;
static xcb_key_symbols_t* keysyms;
static xcb_window_t gWindow;
static xcb_window_t gRootWindow;
static pcSmallRect gWindowSize;
static bool gHasXFixes = false;
static bool gWindowMapped = false;
static bool gPendingActivate = false;
static bool gPendingActivateFlag = false;
static hsSemaphore statusFlag;

// Atoms for talking to the window manager
static xcb_atom_t gAtomWmProtocols;
static xcb_atom_t gAtomWmDeleteWindow;
static xcb_atom_t gAtomNetWmState;
static xcb_atom_t gAtomNetWmStateFullscreen;
static xcb_atom_t gAtomNetWmStateDemandsAttention;
static xcb_atom_t gAtomNetWmName;
static xcb_atom_t gAtomUtf8String;

enum
{
    kArgSkipLoginDialog,
    kArgServerIni,
    kArgLocalData,
    kArgLocalPython,
    kArgLocalSDL,
    kArgPlayerId,
    kArgStartUpAgeName,
    kArgPvdFile,
    kArgSkipIntroMovies,
    kArgRenderer,
    kArgUsername
};

static const plCmdArgDef s_cmdLineArgs[] = {
    { kCmdArgFlagged  | kCmdTypeBool,       "SkipLoginDialog", kArgSkipLoginDialog },
    { kCmdArgFlagged  | kCmdTypeString,     "ServerIni",       kArgServerIni },
    { kCmdArgFlagged  | kCmdTypeBool,       "LocalData",       kArgLocalData   },
    { kCmdArgFlagged  | kCmdTypeBool,       "LocalPython",     kArgLocalPython },
    { kCmdArgFlagged  | kCmdTypeBool,       "LocalSDL",        kArgLocalSDL },
    { kCmdArgFlagged  | kCmdTypeInt,        "PlayerId",        kArgPlayerId },
    { kCmdArgFlagged  | kCmdTypeString,     "Age",             kArgStartUpAgeName },
    { kCmdArgFlagged  | kCmdTypeString,     "PvdFile",         kArgPvdFile },
    { kCmdArgFlagged  | kCmdTypeBool,       "SkipIntroMovies", kArgSkipIntroMovies },
    { kCmdArgFlagged  | kCmdTypeString,     "Renderer",        kArgRenderer },
    { kCmdArgFlagged  | kCmdTypeString,     "Username",        kArgUsername },
};

//
// For error logging
//
static plStatusLog* s_DebugLog = nullptr;
static void _DebugMessageProc(const char* msg)
{
#if defined(HS_DEBUGGING) || !defined(PLASMA_EXTERNAL_RELEASE)
    s_DebugLog->AddLine(plStatusLog::kRed, msg);
#endif // defined(HS_DEBUGGING) || !defined(PLASMA_EXTERNAL_RELEASE)
}

static void _StatusMessageProc(const char* msg)
{
#if defined(HS_DEBUGGING) || !defined(PLASMA_EXTERNAL_RELEASE)
    s_DebugLog->AddLine(msg);
#endif // defined(HS_DEBUGGING) || !defined(PLASMA_EXTERNAL_RELEASE)
}

template<typename... _Args>
static void DebugMsg(const char* format, _Args&&... args)
{
#if defined(HS_DEBUGGING) || !defined(PLASMA_EXTERNAL_RELEASE)
    s_DebugLog->AddLineF(plStatusLog::kYellow, format, std::forward<_Args>(args)...);
#endif // defined(HS_DEBUGGING) || !defined(PLASMA_EXTERNAL_RELEASE)
}

static void DebugInit()
{
#if defined(HS_DEBUGGING) || !defined(PLASMA_EXTERNAL_RELEASE)
    plStatusLogMgr& mgr = plStatusLogMgr::GetInstance();
    s_DebugLog = mgr.CreateStatusLog(30, "plasmadbg.log", plStatusLog::kFilledBackground |
                 plStatusLog::kDeleteForMe | plStatusLog::kAlignToTop | plStatusLog::kTimestamp);
    hsSetDebugMessageProc(_DebugMessageProc);
    hsSetStatusMessageProc(_StatusMessageProc);
#endif // defined(HS_DEBUGGING) || !defined(PLASMA_EXTERNAL_RELEASE)
}

enum
{
    kNetWmStateRemove = 0,
    kNetWmStateAdd = 1
};

static void ISetNetWmState(bool on, xcb_atom_t state)
{
    if (gWindowMapped) {
        /* Mapped windows must ask the window manager via a client message */
        xcb_client_message_event_t event{};
        event.response_type = XCB_CLIENT_MESSAGE;
        event.format = 32;
        event.window = gWindow;
        event.type = gAtomNetWmState;
        event.data.data32[0] = on ? kNetWmStateAdd : kNetWmStateRemove;
        event.data.data32[1] = state;
        xcb_send_event(gXConn, 0, gRootWindow,
                XCB_EVENT_MASK_SUBSTRUCTURE_REDIRECT | XCB_EVENT_MASK_SUBSTRUCTURE_NOTIFY,
                reinterpret_cast<const char*>(&event));
    } else if (on) {
        /* Unmapped windows can have the property set directly */
        xcb_change_property(gXConn, XCB_PROP_MODE_APPEND, gWindow,
                gAtomNetWmState, XCB_ATOM_ATOM, 32, 1, &state);
    }
}

void plClient::IResizeNativeDisplayDevice(int width, int height, bool windowed)
{
    hsStatusMessage(ST::format("Setting window size to {}×{}", width, height).c_str());

    ISetNetWmState(!windowed, gAtomNetWmStateFullscreen);

    const uint32_t values[] = { uint32_t(width), uint32_t(height) };
    xcb_configure_window(gXConn, gWindow,
            XCB_CONFIG_WINDOW_WIDTH | XCB_CONFIG_WINDOW_HEIGHT,
            values);
    xcb_flush(gXConn);

    gWindowSize.fWidth = width;
    gWindowSize.fHeight = height;
}

// Unlike Windows, we never change the display mode. Fullscreen is handled by
// the window manager (_NET_WM_STATE_FULLSCREEN) at the desktop resolution.
void plClient::IChangeResolution(int width, int height) {}

// No portable X11 equivalent of the Windows taskbar progress indicator.
void plClient::IUpdateProgressIndicator(plOperationProgress* progress) {}

void plClient::ShowClientWindow() {
    /* Map the window on the screen */
    xcb_map_window(gXConn, gWindow);
    xcb_flush(gXConn);
    gWindowMapped = true;
}

void plClient::FlashWindow()
{
    ISetNetWmState(true, gAtomNetWmStateDemandsAttention);
    xcb_flush(gXConn);
}


PF_CONSOLE_LINK_ALL();

static hsSsize_t getpassword(char* password)
{
    struct termios old_t, new_t;
    hsSsize_t nsize;

    if (tcgetattr(fileno(stdin), &old_t) != 0)
        return -1;

    new_t = old_t;
    new_t.c_lflag &= ~ECHO;

    if (tcsetattr(fileno(stdin), TCSAFLUSH, &new_t) != 0)
        return -1;

    nsize = fscanf(stdin, "%s", password);

    (void)tcsetattr(fileno(stdin), TCSAFLUSH, &old_t);
    fprintf(stdout, "\n");

    return nsize;
}

static void CalculateHash(const ST::string& username, const ST::string& password, ShaDigest& hash)
{
    //  Hash username and password before sending over the 'net.
    //  -- Legacy compatibility: @gametap (and other usernames with domains in them) need
    //     to be hashed differently.
    static const std::regex re_domain("[^@]+@([^.]+\\.)*([^.]+)\\.[^.]+");
    std::cmatch match;
    std::regex_search(username.c_str(), match, re_domain);
    if (match.empty() || ST::string(match[2].str()).compare_i("gametap") == 0) {
        //  Plain Usernames...
        plSHA1Checksum shasum(password.size(), reinterpret_cast<const uint8_t*>(password.c_str()));
        uint32_t* dest = reinterpret_cast<uint32_t*>(hash);
        const uint32_t* from = reinterpret_cast<const uint32_t*>(shasum.GetValue());

        dest[0] = hsToBE32(from[0]);
        dest[1] = hsToBE32(from[1]);
        dest[2] = hsToBE32(from[2]);
        dest[3] = hsToBE32(from[3]);
        dest[4] = hsToBE32(from[4]);
    }
    else {
        //  Domain-based Usernames...
        CryptHashPassword(username, password, hash);
    }
}

static size_t CurlCallback(void *buffer, size_t size, size_t nmemb, void *param)
{
    static char status[256];

    strncpy(status, (const char *)buffer, std::min<size_t>(size * nmemb, 256));
    status[255] = 0;

    fprintf(stdout, "%s\n\n", status);
    statusFlag.Signal();

    return size * nmemb;
}

static bool ConsoleLoginScreen(const ST::string& cliUsername)
{
    std::thread statusThread = std::thread([]() {
        ST::string statusUrl = GetServerStatusUrl();
        if (statusUrl.empty()) {
            statusFlag.Signal();
            return;
        }

        CURL* hCurl = curl_easy_init();

        // For reporting errors
        char curlError[CURL_ERROR_SIZE];
        curl_easy_setopt(hCurl, CURLOPT_ERRORBUFFER, curlError);
        curl_easy_setopt(hCurl, CURLOPT_FOLLOWLOCATION, 1);
        curl_easy_setopt(hCurl, CURLOPT_MAXREDIRS, 5);
        curl_easy_setopt(hCurl, CURLOPT_URL, statusUrl.c_str());
        curl_easy_setopt(hCurl, CURLOPT_USERAGENT, "UruClient/1.0");
        curl_easy_setopt(hCurl, CURLOPT_WRITEFUNCTION, &CurlCallback);

        if (curl_easy_perform(hCurl) != 0) {
            fprintf(stderr, "%s\n\n", curlError);
            statusFlag.Signal();
        }

        curl_easy_cleanup(hCurl);
    });

    statusFlag.Wait();
    statusThread.join();

    ST::string username = cliUsername;
    if (cliUsername.empty()) {
        fprintf(stdout, "[Use Ctrl+D to cancel]\nUsername or Email: ");
        fflush(stdout);

        char tmpUsername[kMaxAccountNameLength];
        if (fscanf(stdin, "%s", tmpUsername) != 1) {
            return false;
        }
        username = tmpUsername;
    }

    pfPasswordStore* store = pfPasswordStore::Instance();
    ST::string password = store->GetPassword(username);

    if (!password.empty() && cliUsername.empty()) {
        fprintf(stdout, "Use saved password? [y/n] ");
        fflush(stdout);
        char c;
        fscanf(stdin, " %c", &c);
        if (c == 'n' || c == 'N') {
            password = ST_LITERAL("");
        }
        fprintf(stdout, "\n");
    }

    if (password.empty()) {
        fprintf(stdout, "Password: ");
        fflush(stdout);

        char tmpPassword[kMaxPasswordLength];
        getpassword(tmpPassword);
        password = tmpPassword;

        fprintf(stdout, "Save password? [y/n] ");
        fflush(stdout);
        char c;
        fscanf(stdin, " %c", &c);
        if (c == 'y' || c == 'Y') {
            store->SetPassword(username, password);
        }
        fprintf(stdout, "\n");
    }

    ShaDigest namePassHash;
    CalculateHash(username, password, namePassHash);

    NetCommSetAccountUsernamePassword(username, namePassHash);

    char16_t platform[] = u"linux";
    NetCommSetAuthTokenAndOS(nullptr, platform);

    if (!NetCliAuthQueryConnected())
        NetCommConnect();

    NetCommAuthenticate(nullptr);

    while (!NetCommIsLoginComplete()) {
        NetCommUpdate();
    }

    ENetError result = NetCommGetAuthResult();

    if (!IS_NET_SUCCESS(result)) {
        ST::printf(stdout, "{}\n", NetErrorToString(result));
        return false;
    }

    return true;
}

static uint32_t ParseRendererArgument(const ST::string& requested)
{
    using namespace ST::literals;

    static std::unordered_set<ST::string, ST::hash_i, ST::equal_i> dx_args {
        "directx"_st, "direct3d"_st, "dx"_st, "d3d"_st
    };

    static std::unordered_set<ST::string, ST::hash_i, ST::equal_i> gl_args {
        "opengl"_st, "gl"_st
    };

    if (dx_args.find(requested) != dx_args.end())
        return hsG3DDeviceSelector::kDevTypeDirect3D;

    if (gl_args.find(requested) != gl_args.end())
        return hsG3DDeviceSelector::kDevTypeOpenGL;

    return hsG3DDeviceSelector::kDevTypeUnknown;
}

static xcb_atom_t IInternAtom(xcb_connection_t* connection, const char* name)
{
    xcb_intern_atom_cookie_t cookie = xcb_intern_atom(connection, 0, strlen(name), name);
    xcb_intern_atom_reply_t* reply = xcb_intern_atom_reply(connection, cookie, nullptr);
    if (!reply)
        return XCB_ATOM_NONE;

    xcb_atom_t atom = reply->atom;
    free(reply);
    return atom;
}

static bool XInit(xcb_connection_t* connection, Display* display)
{
    gWindowSize.Set(0, 0, 800, 600);

    /* Get the X11 key mappings */
    keysyms = xcb_key_symbols_alloc(connection);

    /* Get the first screen */
    const xcb_setup_t* setup = xcb_get_setup(connection);
    xcb_screen_iterator_t iter = xcb_setup_roots_iterator(setup);
    xcb_screen_t* screen = iter.data;

    /* Check for XFixes support for hiding the cursor */
    const xcb_query_extension_reply_t* qe_reply = xcb_get_extension_data(connection, &xcb_xfixes_id);
    if (qe_reply && qe_reply->present)
    {
        /* We *must* negotiate the XFixes version with the server */
        xcb_xfixes_query_version_cookie_t qv_cookie = xcb_xfixes_query_version(connection, XCB_XFIXES_MAJOR_VERSION, XCB_XFIXES_MINOR_VERSION);
        xcb_xfixes_query_version_reply_t* qv_reply = xcb_xfixes_query_version_reply(connection, qv_cookie, nullptr);

//#ifndef HS_DEBUGGING // Don't hide the cursor when debugging
        gHasXFixes = qv_reply->major_version >= 4;
//#endif

        free(qv_reply);
    }

    const uint32_t event_mask = XCB_EVENT_MASK_EXPOSURE
                              | XCB_EVENT_MASK_KEY_PRESS
                              | XCB_EVENT_MASK_KEY_RELEASE
                              | XCB_EVENT_MASK_POINTER_MOTION
                              | XCB_EVENT_MASK_BUTTON_PRESS
                              | XCB_EVENT_MASK_BUTTON_RELEASE
                              | XCB_EVENT_MASK_ENTER_WINDOW
                              | XCB_EVENT_MASK_LEAVE_WINDOW
                              | XCB_EVENT_MASK_FOCUS_CHANGE
                              | XCB_EVENT_MASK_STRUCTURE_NOTIFY;

    /* Create the window */
    xcb_window_t window = xcb_generate_id(connection);
    xcb_create_window(connection,                    /* Connection          */
                      XCB_COPY_FROM_PARENT,          /* depth (same as root)*/
                      window,                        /* window Id           */
                      screen->root,                  /* parent window       */
                      /* x, y                */
                      gWindowSize.fX, gWindowSize.fY,
                      /* width, height       */
                      gWindowSize.fWidth, gWindowSize.fHeight,
                      0,                             /* border_width        */
                      XCB_WINDOW_CLASS_INPUT_OUTPUT, /* class               */
                      screen->root_visual,           /* visual              */
                      XCB_CW_EVENT_MASK,             /* masks               */
                      &event_mask);                  /* masks               */

    gWindow = window;
    gRootWindow = screen->root;

    gAtomWmProtocols = IInternAtom(connection, "WM_PROTOCOLS");
    gAtomWmDeleteWindow = IInternAtom(connection, "WM_DELETE_WINDOW");
    gAtomNetWmState = IInternAtom(connection, "_NET_WM_STATE");
    gAtomNetWmStateFullscreen = IInternAtom(connection, "_NET_WM_STATE_FULLSCREEN");
    gAtomNetWmStateDemandsAttention = IInternAtom(connection, "_NET_WM_STATE_DEMANDS_ATTENTION");
    gAtomNetWmName = IInternAtom(connection, "_NET_WM_NAME");
    gAtomUtf8String = IInternAtom(connection, "UTF8_STRING");

    /* Ask the window manager to notify us instead of disconnecting us when
     * the user closes the window, so we can shut down cleanly */
    xcb_change_property(connection,
                        XCB_PROP_MODE_REPLACE,
                        window,
                        gAtomWmProtocols,
                        XCB_ATOM_ATOM,
                        32,
                        1,
                        &gAtomWmDeleteWindow);

    ST::string title = ST::format("{}", plProduct::LongName());
    xcb_change_property(connection,
                        XCB_PROP_MODE_REPLACE,
                        window,
                        XCB_ATOM_WM_NAME,
                        XCB_ATOM_STRING,
                        8,
                        title.size(),
                        title.c_str());
    xcb_change_property(connection,
                        XCB_PROP_MODE_REPLACE,
                        window,
                        gAtomNetWmName,
                        gAtomUtf8String,
                        8,
                        title.size(),
                        title.c_str());

    static const char wmClass[] = "plClient\0Plasma";
    xcb_change_property(connection,
                        XCB_PROP_MODE_REPLACE,
                        window,
                        XCB_ATOM_WM_CLASS,
                        XCB_ATOM_STRING,
                        8,
                        sizeof(wmClass),
                        wmClass);
    xcb_flush(connection);

    gClient.SetClientWindow((hsWindowHndl)(uintptr_t)window);
    gClient.SetClientDisplay((hsWindowHndl)display);
    gClient.Init();
    return true;
}

static void PumpMessageQueueProc()
{
    static const unsigned char KEYCODE_LINUX_TO_HID[256] = {
        0,41,30,31,32,33,34,35,36,37,38,39,45,46,42,43,20,26,8,21,23,28,24,12,18,19,
        47,48,158,224,4,22,7,9,10,11,13,14,15,51,52,53,225,49,29,27,6,25,5,17,16,54,
        55,56,229,85,226,44,57,58,59,60,61,62,63,64,65,66,67,83,71,95,96,97,86,92,
        93,94,87,89,90,91,98,99,0,0,100,68,69,0,0,0,0,0,0,0,88,228,84,154,230,0,74,
        82,75,80,79,77,81,78,73,76,0,0,0,0,0,103,0,72,0,0,0,0,0,227,231,0,0,0,0,0,0,
        0,0,0,0,0,0,118,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
        0,0,0,0,0,0,0,0,0,0,0,0,0,104,105,106,107,108,109,110,111,112,113,114,115,0,
        0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
        0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
    };

    xcb_generic_event_t* event;
    xcb_generic_event_t* nextEvent = nullptr;
    while ((event = (nextEvent ? nextEvent : xcb_poll_for_event(gXConn)))) {
        nextEvent = nullptr;

        switch (event->response_type & ~0x80)
        {
        case XCB_CONFIGURE_NOTIFY: // Window resize
            {
                xcb_configure_notify_event_t* cne = reinterpret_cast<xcb_configure_notify_event_t*>(event);
                bool sizeChanged = cne->width != gWindowSize.fWidth || cne->height != gWindowSize.fHeight;
                gWindowSize.Set(cne->x, cne->y, cne->width, cne->height);

                if (sizeChanged && gClient && gClient->GetPipeline())
                    gClient->GetPipeline()->Resize(cne->width, cne->height);
            }
            break;

        case XCB_CLIENT_MESSAGE: // Window manager requests (e.g. window close)
            {
                xcb_client_message_event_t* cme = reinterpret_cast<xcb_client_message_event_t*>(event);
                if (cme->type == gAtomWmProtocols && cme->data.data32[0] == gAtomWmDeleteWindow) {
                    if (gClient) {
                        gClient->SetDone(true);
                        if (plNetClientMgr* mgr = plNetClientMgr::GetInstance())
                            mgr->QueueDisableNet(false, nullptr);
                    }
                }
            }
            break;

        case XCB_FOCUS_IN:
        case XCB_FOCUS_OUT:
            {
                xcb_focus_in_event_t* fe = reinterpret_cast<xcb_focus_in_event_t*>(event);

                /* Ignore focus changes caused by pointer/keyboard grabs
                 * (e.g. every mouse click) - only real focus counts */
                if (fe->mode == XCB_NOTIFY_MODE_GRAB || fe->mode == XCB_NOTIFY_MODE_UNGRAB)
                    break;

                bool active = (event->response_type & ~0x80) == XCB_FOCUS_IN;
                if (gClient && !gClient->GetDone()) {
                    gClient->WindowActivate(active);
                } else {
                    gPendingActivate = true;
                    gPendingActivateFlag = active;
                }
            }
            break;

        case XCB_KEY_PRESS:     // Keyboard key press
        case XCB_KEY_RELEASE:   // Keyboard key release
            {
                xcb_key_press_event_t* kbe = reinterpret_cast<xcb_key_press_event_t*>(event);

                bool down = (kbe->response_type & ~0x80) == XCB_KEY_PRESS;
                bool repeat = false;

                /* X11 reports autorepeat as a release+press pair with
                 * identical timestamps: collapse it into a single repeated
                 * key press */
                if (!down) {
                    nextEvent = xcb_poll_for_event(gXConn);
                    if (nextEvent && (nextEvent->response_type & ~0x80) == XCB_KEY_PRESS) {
                        xcb_key_press_event_t* nke = reinterpret_cast<xcb_key_press_event_t*>(nextEvent);
                        if (nke->detail == kbe->detail && nke->time == kbe->time) {
                            free(nextEvent);
                            nextEvent = nullptr;
                            down = true;
                            repeat = true;
                        }
                    }
                }

                /* X11 offsets Linux keycodes by 8 */
                uint32_t keycode = kbe->detail - 8;
                plKeyDef key = KEY_UNMAPPED;
                if (keycode < 256)
                    key = (plKeyDef)KEYCODE_LINUX_TO_HID[keycode];

                if (down)
                    gClient->SetQuitIntro(true);

                wchar_t c = 0;
                xcb_keysym_t sym = xcb_key_press_lookup_keysym(keysyms, kbe, (kbe->state & XCB_MOD_MASK_SHIFT));

                gClient->GetInputManager()->HandleKeyEvent(key, down, repeat, c);

                if (down && !xcb_is_cursor_key(sym) && !xcb_is_modifier_key(sym) && !xcb_is_function_key(sym) && !std::iscntrl((wchar_t)sym)) {
                    c = wchar_t(sym);
                    gClient->GetInputManager()->HandleKeyEvent(key, down, repeat, c);
                }
            }
            break;

        case XCB_MOTION_NOTIFY: // Mouse Movement
            {
                xcb_motion_notify_event_t* me = reinterpret_cast<xcb_motion_notify_event_t*>(event);

                plIMouseXEventMsg* pXMsg = new plIMouseXEventMsg;
                plIMouseYEventMsg* pYMsg = new plIMouseYEventMsg;

                pXMsg->fWx = me->event_x;
                pXMsg->fX = (float)me->event_x / (float)gWindowSize.fWidth;

                pYMsg->fWy = me->event_y;
                pYMsg->fY = (float)me->event_y / (float)gWindowSize.fHeight;

                gClient->GetInputManager()->MsgReceive(pXMsg);
                gClient->GetInputManager()->MsgReceive(pYMsg);

                /* When mouse-look is active, keep the pointer away from the
                 * window edges so relative movement never runs out of room */
                if (plInputManager::RecenterMouse()) {
                    int16_t newX = me->event_x;
                    int16_t newY = me->event_y;

                    if (pXMsg->fX <= 0.1f || pXMsg->fX >= 0.9f) {
                        newX = gWindowSize.fWidth / 2;
                        pXMsg->fWx = newX;
                        pXMsg->fX = (float)newX / (float)gWindowSize.fWidth;
                        gClient->GetInputManager()->MsgReceive(pXMsg);
                    }

                    if (pYMsg->fY <= 0.1f || pYMsg->fY >= 0.9f) {
                        newY = gWindowSize.fHeight / 2;
                        pYMsg->fWy = newY;
                        pYMsg->fY = (float)newY / (float)gWindowSize.fHeight;
                        gClient->GetInputManager()->MsgReceive(pYMsg);
                    }

                    if (newX != me->event_x || newY != me->event_y) {
                        xcb_warp_pointer(gXConn, XCB_NONE, gWindow, 0, 0, 0, 0, newX, newY);
                        xcb_flush(gXConn);
                    }
                }

                delete(pXMsg);
                delete(pYMsg);
            }
            break;

        case XCB_BUTTON_PRESS:
            {
                xcb_button_press_event_t* bpe = reinterpret_cast<xcb_button_press_event_t*>(event);

                /* Handle scroll wheel */
                if (bpe->detail == XCB_BUTTON_INDEX_4 || bpe->detail == XCB_BUTTON_INDEX_5)
                {
                    plMouseEventMsg* pMsg = new plMouseEventMsg;
                    if (bpe->detail == XCB_BUTTON_INDEX_4) {
                        pMsg->SetButton(kWheelPos);
                        pMsg->SetWheelDelta(120.0f);
                    } else {
                        pMsg->SetButton(kWheelNeg);
                        pMsg->SetWheelDelta(-120.0f);
                    }
                    pMsg->SetXPos((float)bpe->event_x / (float)gWindowSize.fWidth);
                    pMsg->SetYPos((float)bpe->event_y / (float)gWindowSize.fHeight);
                    pMsg->Send();
                    break;
                }

                /* Emulate the Windows double click messages */
                static xcb_timestamp_t lastClickTime = 0;
                static xcb_button_t lastClickButton = 0;
                bool dblClick = bpe->detail == lastClickButton && bpe->time - lastClickTime <= 500;
                lastClickButton = bpe->detail;
                lastClickTime = dblClick ? 0 : bpe->time;

                plIMouseXEventMsg* pXMsg = new plIMouseXEventMsg;
                plIMouseYEventMsg* pYMsg = new plIMouseYEventMsg;
                plIMouseBEventMsg* pBMsg = new plIMouseBEventMsg;

                pXMsg->fWx = bpe->event_x;
                pXMsg->fX = (float)bpe->event_x / (float)gWindowSize.fWidth;

                pYMsg->fWy = bpe->event_y;
                pYMsg->fY = (float)bpe->event_y / (float)gWindowSize.fHeight;

                switch (bpe->detail) {
                case XCB_BUTTON_INDEX_1:
                    pBMsg->fButton |= kLeftButtonDown;
                    if (dblClick)
                        pBMsg->fButton |= kLeftButtonDblClk;
                    break;
                case XCB_BUTTON_INDEX_2:
                    pBMsg->fButton |= kMiddleButtonDown;
                    break;
                case XCB_BUTTON_INDEX_3:
                    pBMsg->fButton |= kRightButtonDown;
                    if (dblClick)
                        pBMsg->fButton |= kRightButtonDblClk;
                    break;
                default:
                    break;
                }

                gClient->SetQuitIntro(true);
                gClient->GetInputManager()->MsgReceive(pXMsg);
                gClient->GetInputManager()->MsgReceive(pYMsg);
                gClient->GetInputManager()->MsgReceive(pBMsg);

                delete(pXMsg);
                delete(pYMsg);
                delete(pBMsg);
            }
            break;

        case XCB_BUTTON_RELEASE:
            {
                xcb_button_release_event_t* bre = reinterpret_cast<xcb_button_release_event_t*>(event);

                /* The scroll wheel is handled entirely on button press */
                if (bre->detail == XCB_BUTTON_INDEX_4 || bre->detail == XCB_BUTTON_INDEX_5)
                    break;

                plIMouseXEventMsg* pXMsg = new plIMouseXEventMsg;
                plIMouseYEventMsg* pYMsg = new plIMouseYEventMsg;
                plIMouseBEventMsg* pBMsg = new plIMouseBEventMsg;

                pXMsg->fWx = bre->event_x;
                pXMsg->fX = (float)bre->event_x / (float)gWindowSize.fWidth;

                pYMsg->fWy = bre->event_y;
                pYMsg->fY = (float)bre->event_y / (float)gWindowSize.fHeight;

                switch (bre->detail) {
                case XCB_BUTTON_INDEX_1:
                    pBMsg->fButton |= kLeftButtonUp;
                    break;
                case XCB_BUTTON_INDEX_2:
                    pBMsg->fButton |= kMiddleButtonUp;
                    break;
                case XCB_BUTTON_INDEX_3:
                    pBMsg->fButton |= kRightButtonUp;
                    break;
                default:
                    break;
                }

                gClient->GetInputManager()->MsgReceive(pXMsg);
                gClient->GetInputManager()->MsgReceive(pYMsg);
                gClient->GetInputManager()->MsgReceive(pBMsg);

                delete(pXMsg);
                delete(pYMsg);
                delete(pBMsg);
            }
            break;

        case XCB_ENTER_NOTIFY: // Mouse over windows
            {
                if (gHasXFixes)
                {
                    xcb_enter_notify_event_t* ene = reinterpret_cast<xcb_enter_notify_event_t*>(event);
                    xcb_xfixes_hide_cursor(gXConn, ene->root);
                    xcb_flush(gXConn);
                }
            }
            break;

        case XCB_LEAVE_NOTIFY: // Mouse off windows
            {
                if (gHasXFixes)
                {
                    xcb_leave_notify_event_t* lne = reinterpret_cast<xcb_leave_notify_event_t*>(event);
                    xcb_xfixes_show_cursor(gXConn, lne->root);
                    xcb_flush(gXConn);
                }
            }
            break;

        default:
            break;
        }

        free(event);
    }
}

// Stub main function so it compiles on non-Windows
int main(int argc, const char** argv)
{
    PF_CONSOLE_INIT_ALL();

    std::vector<ST::string> args;
    args.reserve(argc);
    for (size_t i = 0; i < argc; i++) {
        args.push_back(ST::string::from_utf8(argv[i]));
    }

    plCmdParser cmdParser(s_cmdLineArgs, std::size(s_cmdLineArgs));
    cmdParser.Parse(args);

    bool doIntroDialogs = true;
    ST::string cliUsername;
#ifndef PLASMA_EXTERNAL_RELEASE
    if (cmdParser.IsSpecified(kArgSkipLoginDialog))
        doIntroDialogs = false;
    if (cmdParser.IsSpecified(kArgLocalData))
    {
        gDataServerLocal = true;
        gPythonLocal = true;
    }
    if (cmdParser.IsSpecified(kArgLocalPython))
        gPythonLocal = true;
    if (cmdParser.IsSpecified(kArgLocalSDL))
        gSDLLocal = true;
    if (cmdParser.IsSpecified(kArgPlayerId))
        NetCommSetIniPlayerId(cmdParser.GetInt(kArgPlayerId));
    if (cmdParser.IsSpecified(kArgStartUpAgeName))
        NetCommSetIniStartUpAge(cmdParser.GetString(kArgStartUpAgeName));
    if (cmdParser.IsSpecified(kArgPvdFile))
        plPXSimulation::SetDefaultDebuggerEndpoint(cmdParser.GetString(kArgPvdFile));
    if (cmdParser.IsSpecified(kArgRenderer))
        gClient.SetRequestedRenderingBackend(ParseRendererArgument(cmdParser.GetString(kArgRenderer)));
    if (cmdParser.IsSpecified(kArgUsername))
        cliUsername = cmdParser.GetString(kArgUsername);
#endif

    plFileName serverIni = "server.ini";
    if (cmdParser.IsSpecified(kArgServerIni))
        serverIni = cmdParser.GetString(kArgServerIni);

    // Load an optional general.ini
    plFileName gipath = plFileName::Join(plFileSystem::GetInitPath(), "general.ini");
    FILE *generalini = plFileSystem::Open(gipath, "rb");
    if (generalini)
    {
        fclose(generalini);
        pfConsoleEngine tempConsole;
        tempConsole.ExecuteFile(gipath);
    }

    // Set up to log errors by using hsDebugMessage
    DebugInit();
    DebugMsg("Plasma 2.0.{}.{} - {}", PLASMA2_MAJOR_VERSION, PLASMA2_MINOR_VERSION, plProduct::ProductString());

    FILE* serverIniFile = plFileSystem::Open(serverIni, "rb");
    if (serverIniFile) {
        fclose(serverIniFile);
        try {
            pfServerIni::Load(serverIni);
        } catch (const pfServerIniParseException& exc) {
            hsMessageBox(ST::format("Error in server.ini file. Please check your URU installation.\n{}", exc.what()), ST_LITERAL("Error"), hsMessageBoxNormal);
            return 1;
        }
    } else {
        hsMessageBox(ST_LITERAL("No server.ini file found. Please check your URU installation."), ST_LITERAL("Error"), hsMessageBoxNormal);
        return 1;
    }

    if (!XInitThreads()) {
        hsMessageBox("Failed to initialize plClient", "Error", hsMessageBoxNormal);
        return 1;
    }

    /* Open the connection to the X server */
    gDisplay = XOpenDisplay(nullptr);
    if (!gDisplay) {
        hsMessageBox("Failed to open X display", "Error", hsMessageBoxNormal);
        return 1;
    }
    gXConn = XGetXCBConnection(gDisplay);
    XSetEventQueueOwner(gDisplay, XCBOwnsEventQueue);

    if (!XInit(gXConn, gDisplay)) {
        hsMessageBox("Failed to initialize plClient", "Error", hsMessageBoxNormal);
        return 1;
    }

    NetCliAuthAutoReconnectEnable(false);
    NetCommStartup();

    curl_global_init(CURL_GLOBAL_ALL);

    // Login stuff
    if (!ConsoleLoginScreen(cliUsername)) {
        gClient.ShutdownStart();
        gClient.ShutdownEnd();
        NetCommShutdown();

        XCloseDisplay(gDisplay);

        return 0;
    }

    curl_global_cleanup();

    NetCliAuthAutoReconnectEnable(true);

    // We should quite frankly be done initing the client by now. But, if not, spawn the good old
    // "Starting URU, please wait..." dialog (not so yay)
    if (!gClient.IsInited()) {
        //HWND splashDialog = ::CreateDialog(hInst, MAKEINTRESOURCE(IDD_LOADING), nullptr, SplashDialogProc);
        gClient.Wait();
        //::DestroyWindow(splashDialog);
    }

    // Main loop
    if (gClient && !gClient->GetDone()) {
        // Must be done here due to the plClient* dereference.
        if (cmdParser.IsSpecified(kArgSkipIntroMovies))
            gClient->SetFlag(plClient::kFlagSkipIntroMovies);

        if (gPendingActivate)
            gClient->WindowActivate(gPendingActivateFlag);

        gClient->SetMessagePumpProc(PumpMessageQueueProc);
        gClient.Start();

        do {
            gClient->MainLoop();
            if (gClient->GetDone()) {
                gClient.ShutdownStart();
                break;
            }

            PumpMessageQueueProc();
        } while (true);
    }

    gClient.ShutdownEnd();
    NetCommShutdown();

    XCloseDisplay(gDisplay);

    return 0;
}
