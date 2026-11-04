$src  = "$env:TEMP\rbx_esp.cpp"
$exe  = "$env:TEMP\rbx_esp.exe"
$ghost= "$env:SystemRoot\Temp\svchost_tmp.exe"

$code = @'
#define NOMINMAX
#define WIN32_LEAN_AND_MEAN
#include <Windows.h>
#include <TlHelp32.h>
#include <string>
#include <vector>
#include <thread>
#include <mutex>
#include <atomic>
#include <cmath>
#include <algorithm>
#include <cstring>
#pragma comment(lib, "user32.lib")
#pragma comment(lib, "gdi32.lib")

constexpr uintptr_t OFF_FakeDM_Ptr    = 147875328;
constexpr uintptr_t OFF_FakeDM_Real   = 504;
constexpr uintptr_t OFF_VE_Ptr        = 142189080;
constexpr uintptr_t OFF_VE_VM         = 432;
constexpr uintptr_t OFF_VE_Dims       = 2832;
constexpr uintptr_t OFF_DM_WS         = 328;
constexpr uintptr_t OFF_WS_Cam        = 1184;
constexpr uintptr_t OFF_Inst_NameCont = 104;
constexpr uintptr_t OFF_Inst_Name     = 0;
constexpr uintptr_t OFF_Inst_Children = 112;
constexpr uintptr_t OFF_Inst_ClassDesc= 24;
constexpr uintptr_t OFF_Inst_ClassName= 8;
constexpr uintptr_t OFF_Str_Len       = 16;
constexpr uintptr_t OFF_Pl_LP         = 280;
constexpr uintptr_t OFF_Pl_Model      = 672;
constexpr uintptr_t OFF_Pl_Name       = 288;
constexpr uintptr_t OFF_Pl_TeamColor  = 952;
constexpr uintptr_t OFF_Model_Primary = 576;
constexpr uintptr_t OFF_Hum_HP        = 388;
constexpr uintptr_t OFF_Hum_MaxHP     = 412;
constexpr uintptr_t OFF_BP_Prim       = 376;
constexpr uintptr_t OFF_Prim_Pos      = 212;

constexpr float MAX_DIST     = 1000.f;
constexpr int   MAX_PLAYERS  = 100;
constexpr int   CHAIN_MS     = 1000;
constexpr int   POS_MS       = 8;
constexpr int   RENDER_MS    = 8;

// ── Triggerbot ───────────────────────────────────────────────────────────────
constexpr float TRIGGER_RADIUS   = 60.f;  // px do centro da tela ate o centro da box
constexpr int   TRIGGER_DELAY    = 12;    // ms entre LEFTDOWN e LEFTUP
constexpr int   TRIGGER_COOLDOWN = 85;    // ms entre disparos consecutivos
constexpr int   TRIGGER_POLL     = 4;     // ms de poll do botao
// MB4 = VK_XBUTTON1 (0x05)  MB5 = VK_XBUTTON2 (0x06)
// ─────────────────────────────────────────────────────────────────────────────

static const wchar_t* KILL_FLAG = L"C:\\Windows\\Temp\\byp_kill.flag";
static const wchar_t* AUTH_FLAG = L"C:\\Windows\\Temp\\byp_auth.flag";

static void WriteKillFlag(){
    HANDLE h=CreateFileW(KILL_FLAG,GENERIC_WRITE,0,nullptr,CREATE_ALWAYS,FILE_ATTRIBUTE_NORMAL,nullptr);
    if(h!=INVALID_HANDLE_VALUE){DWORD w=0;WriteFile(h,"1",1,&w,nullptr);CloseHandle(h);}
    DeleteFileW(AUTH_FLAG);
}

static ULONGLONG GetBootEpoch(){
    FILETIME ft; GetSystemTimeAsFileTime(&ft);
    ULARGE_INTEGER now; now.LowPart=ft.dwLowDateTime; now.HighPart=ft.dwHighDateTime;
    ULONGLONG uptimeHns = GetTickCount64() * 10000ULL;
    return now.QuadPart - uptimeHns;
}

struct AuthPayload { ULONGLONG boot; WCHAR host[64]; };

static void WriteAuthFlag(){
    AuthPayload p{}; p.boot=GetBootEpoch();
    DWORD sz=64; GetComputerNameW(p.host,&sz);
    HANDLE h=CreateFileW(AUTH_FLAG,GENERIC_WRITE,0,nullptr,CREATE_ALWAYS,FILE_ATTRIBUTE_NORMAL,nullptr);
    if(h!=INVALID_HANDLE_VALUE){DWORD w=0;WriteFile(h,&p,sizeof(p),&w,nullptr);CloseHandle(h);}
}

static bool AuthFlagValid(){
    HANDLE h=CreateFileW(AUTH_FLAG,GENERIC_READ,FILE_SHARE_READ,nullptr,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,nullptr);
    if(h==INVALID_HANDLE_VALUE) return false;
    AuthPayload p{}; DWORD r=0;
    ReadFile(h,&p,sizeof(p),&r,nullptr);
    CloseHandle(h);
    if(r!=sizeof(p)) return false;
    WCHAR curHost[64]{}; DWORD sz=64; GetComputerNameW(curHost,&sz);
    if(_wcsicmp(p.host,curHost)!=0) return false;
    ULONGLONG boot=GetBootEpoch();
    ULONGLONG diff=(boot>p.boot)?(boot-p.boot):(p.boot-boot);
    return diff < 300000000ULL;
}

struct PlayerCache{uintptr_t hrp,head,foot,humanoid;float maxhp;uint32_t teamColor;char name[64];};
static PlayerCache g_cache[MAX_PLAYERS];
static int g_cacheCount=0;
static std::mutex g_cacheMtx;
static std::atomic<uint32_t> g_localTC{0};

struct ESPEntry{char name[64];float hp,maxhp,dist,hx,hy,fx,fy;bool sameTeam;};
static ESPEntry g_bufA[MAX_PLAYERS],g_bufB[MAX_PLAYERS];
static ESPEntry *g_wBuf=g_bufA,*g_rBuf=g_bufB;
static int g_rCount=0;
static std::mutex g_frameMtx;

HANDLE g_proc=nullptr;
uintptr_t g_base=0;
HWND g_overlay=nullptr,g_roblox=nullptr;
std::atomic<bool> g_running{true};
static HHOOK g_kbHook=nullptr;
static HHOOK g_mouseHook=nullptr;
static std::atomic<bool> g_mb5{false};
static HDC g_mdc=nullptr;
static HBITMAP g_bmp=nullptr;
static int g_bmpW=0,g_bmpH=0;
static HFONT g_font=nullptr;
static ESPEntry g_snap[MAX_PLAYERS];
static int g_snapCnt=0;

// ── Custom Login UI ──────────────────────────────────────────────────────────
static bool      g_loginOK   = false;
static HINSTANCE g_loginInst = nullptr;
static HWND      g_hUser     = nullptr;
static HWND      g_hPass     = nullptr;
static HFONT     g_fontTitle = nullptr;
static HFONT     g_fontText  = nullptr;
static HBRUSH    g_bgBrush   = nullptr;

static LRESULT CALLBACK LoginWndProc(HWND hw,UINT msg,WPARAM wp,LPARAM lp){
    switch(msg){
    case WM_CREATE:{
        g_hUser = CreateWindowExW(0,L"EDIT",L"",WS_CHILD|WS_VISIBLE|ES_AUTOHSCROLL,40,202,270,24,hw,(HMENU)101,g_loginInst,nullptr);
        g_hPass = CreateWindowExW(0,L"EDIT",L"",WS_CHILD|WS_VISIBLE|ES_PASSWORD|ES_AUTOHSCROLL,40,272,270,24,hw,(HMENU)102,g_loginInst,nullptr);
        HRGN r1 = CreateRoundRectRgn(0, 0, 271, 25, 8, 8);
        SetWindowRgn(g_hUser, r1, TRUE);
        HRGN r2 = CreateRoundRectRgn(0, 0, 271, 25, 8, 8);
        SetWindowRgn(g_hPass, r2, TRUE);
        HWND btn = CreateWindowExW(0,L"BUTTON",L"Login",WS_CHILD|WS_VISIBLE|BS_OWNERDRAW,40,335,270,38,hw,(HMENU)103,g_loginInst,nullptr);
        SendMessage(g_hUser, WM_SETFONT, (WPARAM)g_fontText, TRUE);
        SendMessage(g_hPass, WM_SETFONT, (WPARAM)g_fontText, TRUE);
        SendMessage(btn,     WM_SETFONT, (WPARAM)g_fontText, TRUE);
        SetFocus(g_hUser);
        return 0;
    }
    case WM_CTLCOLOREDIT: {
        SetTextColor((HDC)wp, RGB(255, 255, 255));
        SetBkColor((HDC)wp, RGB(0, 0, 0));
        return (LRESULT)g_bgBrush;
    }
    case WM_DRAWITEM: {
        LPDRAWITEMSTRUCT pDIS = (LPDRAWITEMSTRUCT)lp;
        if (pDIS->CtlID == 103) {
            FillRect(pDIS->hDC, &pDIS->rcItem, g_bgBrush);
            HPEN hPen = CreatePen(PS_SOLID, 1, RGB(50, 50, 50));
            HGDIOBJ oldPen = SelectObject(pDIS->hDC, hPen);
            HGDIOBJ oldBrush = SelectObject(pDIS->hDC, g_bgBrush);
            RoundRect(pDIS->hDC, pDIS->rcItem.left, pDIS->rcItem.top, pDIS->rcItem.right, pDIS->rcItem.bottom, 8, 8);
            SelectObject(pDIS->hDC, oldPen);
            SelectObject(pDIS->hDC, oldBrush);
            DeleteObject(hPen);
            SetBkMode(pDIS->hDC, TRANSPARENT);
            SetTextColor(pDIS->hDC, RGB(255, 255, 255));
            SelectObject(pDIS->hDC, g_fontText);
            DrawTextW(pDIS->hDC, L"Login", -1, &pDIS->rcItem, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
        }
        return TRUE;
    }
    case WM_PAINT: {
        PAINTSTRUCT ps;
        HDC hdc = BeginPaint(hw, &ps);
        FillRect(hdc, &ps.rcPaint, g_bgBrush);
        SetBkMode(hdc, TRANSPARENT);
        HPEN hPen = CreatePen(PS_SOLID, 1, RGB(40, 40, 40));
        HGDIOBJ oldPen = SelectObject(hdc, hPen);
        SelectObject(hdc, g_fontTitle);
        SetTextColor(hdc, RGB(220, 220, 220));
        RECT rcTitle = {20, 15, 330, 40};
        DrawTextW(hdc, L"Blackfade - Authentication", -1, &rcTitle, DT_LEFT | DT_SINGLELINE);
        MoveToEx(hdc, 20, 45, nullptr);
        LineTo(hdc, 330, 45);
        SelectObject(hdc, g_fontText);
        SetTextColor(hdc, RGB(150, 150, 150));
        RECT rcUser = {40, 178, 300, 198};
        DrawTextW(hdc, L"Username", -1, &rcUser, DT_LEFT | DT_SINGLELINE);
        RECT rcPass = {40, 248, 300, 268};
        DrawTextW(hdc, L"Password", -1, &rcPass, DT_LEFT | DT_SINGLELINE);
        HBRUSH editBg = CreateSolidBrush(RGB(0, 0, 0));
        HGDIOBJ oldB = SelectObject(hdc, editBg);
        RoundRect(hdc, 39, 201, 311, 227, 8, 8);
        RoundRect(hdc, 39, 271, 311, 297, 8, 8);
        SelectObject(hdc, oldB);
        DeleteObject(editBg);
        MoveToEx(hdc, 20, 405, nullptr);
        LineTo(hdc, 330, 405);
        SelectObject(hdc, g_fontText);
        SetTextColor(hdc, RGB(80, 80, 80));
        RECT rcFoot = {20, 420, 330, 440};
        DrawTextW(hdc, L"Latest Update: [01/15/2026] - Up to date!", -1, &rcFoot, DT_LEFT | DT_SINGLELINE);
        SelectObject(hdc, oldPen);
        DeleteObject(hPen);
        EndPaint(hw, &ps);
        return 0;
    }
    case WM_NCHITTEST: {
        LRESULT hit = DefWindowProcW(hw, msg, wp, lp);
        if (hit == HTCLIENT) {
            POINT pt = { LOWORD(lp), HIWORD(lp) };
            ScreenToClient(hw, &pt);
            if (pt.y < 45) return HTCAPTION;
        }
        return hit;
    }
    case WM_LBUTTONDOWN: {
        int x = LOWORD(lp), y = HIWORD(lp);
        if (y < 45 && x > 310) DestroyWindow(hw);
        return 0;
    }
    case WM_COMMAND:{
        WORD id=LOWORD(wp);
        if(id==103){
            char u[64]{},p[64]{};
            GetWindowTextA(g_hUser,u,sizeof(u));
            GetWindowTextA(g_hPass,p,sizeof(p));
            if(strcmp(u,"Blackfade")==0&&strcmp(p,"nightshadegoat")==0){
                g_loginOK=true; WriteAuthFlag(); DestroyWindow(hw);
            } else {
                MessageBoxA(hw,"Invalid credentials.","Access denied",MB_OK|MB_ICONERROR);
                SetWindowTextA(g_hPass,""); SetFocus(g_hPass);
            }
            return 0;
        }
        break;
    }
    case WM_DESTROY: PostQuitMessage(0); return 0;
    }
    return DefWindowProcW(hw,msg,wp,lp);
}

static bool ShowLoginDialog(HINSTANCE hInst){
    g_loginInst=hInst;
    static const wchar_t* CLS=L"BlackfadeLogin";
    WNDCLASSEXW wc{sizeof(wc)};
    wc.lpfnWndProc=LoginWndProc; wc.hInstance=hInst;
    wc.hCursor=LoadCursor(nullptr,IDC_ARROW);
    wc.hbrBackground=nullptr;
    wc.lpszClassName=CLS;
    RegisterClassExW(&wc);
    g_bgBrush  = CreateSolidBrush(RGB(0, 0, 0));
    g_fontTitle= CreateFontW(16,0,0,0,FW_BOLD,  0,0,0,DEFAULT_CHARSET,0,0,CLEARTYPE_QUALITY,0,L"Segoe UI");
    g_fontText = CreateFontW(14,0,0,0,FW_NORMAL,0,0,0,DEFAULT_CHARSET,0,0,CLEARTYPE_QUALITY,0,L"Segoe UI");
    int sw=GetSystemMetrics(SM_CXSCREEN),sh=GetSystemMetrics(SM_CYSCREEN);
    int W=350,H=480;
    HWND dlg=CreateWindowExW(WS_EX_TOPMOST,CLS,L"Blackfade Auth",
        WS_POPUP|WS_VISIBLE,(sw-W)/2,(sh-H)/2,W,H,nullptr,nullptr,hInst,nullptr);
    if(!dlg){ UnregisterClassW(CLS,hInst); return false; }
    MSG m{};
    while(GetMessageW(&m,nullptr,0,0)){
        if(!IsDialogMessageW(dlg,&m)){ TranslateMessage(&m); DispatchMessageW(&m); }
    }
    DeleteObject(g_bgBrush);
    DeleteObject(g_fontTitle);
    DeleteObject(g_fontText);
    UnregisterClassW(CLS,hInst);
    return g_loginOK;
}
// ─────────────────────────────────────────────────────────────────────────────

// ── Mouse hook — rastreia MB5 (XBUTTON2) de forma confiavel ─────────────────
static LRESULT CALLBACK MouseProc(int code, WPARAM wp, LPARAM lp){
    if(code == HC_ACTION){
        MSLLHOOKSTRUCT* ms = (MSLLHOOKSTRUCT*)lp;
        if(wp == WM_XBUTTONDOWN && HIWORD(ms->mouseData) == XBUTTON2) g_mb5 = true;
        if(wp == WM_XBUTTONUP   && HIWORD(ms->mouseData) == XBUTTON2) g_mb5 = false;
    }
    return CallNextHookEx(g_mouseHook, code, wp, lp);
}
// ─────────────────────────────────────────────────────────────────────────────

static LRESULT CALLBACK KbProc(int code,WPARAM wp,LPARAM lp){
    if(code==HC_ACTION&&wp==WM_KEYDOWN){
        KBDLLHOOKSTRUCT* kb=(KBDLLHOOKSTRUCT*)lp;
        if(kb->vkCode==VK_F4){
            WriteKillFlag(); g_running=false;
            PostMessage(g_overlay,WM_DESTROY,0,0);
        }
    }
    return CallNextHookEx(g_kbHook,code,wp,lp);
}

template<typename T> __forceinline T RPM(uintptr_t addr){T v{};ReadProcessMemory(g_proc,(LPCVOID)addr,&v,sizeof(T),nullptr);return v;}
static std::string ReadRBXStr(uintptr_t c){uint32_t len=RPM<uint32_t>(c+OFF_Str_Len);if(!len||len>256)return "";char buf[257]{};uintptr_t ptr=(len<16)?c:RPM<uintptr_t>(c);ReadProcessMemory(g_proc,(LPCVOID)ptr,buf,(std::min)(len,255u),nullptr);return std::string(buf,len);}
static uintptr_t GetBase(DWORD pid){HANDLE s=CreateToolhelp32Snapshot(TH32CS_SNAPMODULE|TH32CS_SNAPMODULE32,pid);MODULEENTRY32W me{sizeof(me)};uintptr_t b=0;if(Module32FirstW(s,&me))do{if(_wcsicmp(me.szModule,L"RobloxPlayerBeta.exe")==0){b=(uintptr_t)me.modBaseAddr;break;}}while(Module32NextW(s,&me));CloseHandle(s);return b;}
static std::string GetName(uintptr_t i){uintptr_t nc=RPM<uintptr_t>(i+OFF_Inst_NameCont);if(!nc)return "";return ReadRBXStr(nc+OFF_Inst_Name);}
static std::string GetClass(uintptr_t i){uintptr_t d=RPM<uintptr_t>(i+OFF_Inst_ClassDesc);if(!d)return "";uintptr_t p=RPM<uintptr_t>(d+OFF_Inst_ClassName);if(!p)return "";char b[64]{};ReadProcessMemory(g_proc,(LPCVOID)p,b,63,nullptr);return std::string(b);}
static std::vector<uintptr_t> GetChildren(uintptr_t inst){std::vector<uintptr_t> out;uintptr_t vec=RPM<uintptr_t>(inst+OFF_Inst_Children);if(!vec)return out;uintptr_t s=RPM<uintptr_t>(vec),e=RPM<uintptr_t>(vec+8);if(!s||e<=s)return out;size_t n=(std::min)((e-s)/8,(size_t)(MAX_PLAYERS*3));out.reserve(n);for(size_t i=0;i<n;i++){uintptr_t c=RPM<uintptr_t>(s+i*8);if(c)out.push_back(c);}return out;}
static uintptr_t FindClass(uintptr_t p,const char* c){for(auto x:GetChildren(p))if(GetClass(x)==c)return x;return 0;}
static uintptr_t FindName(uintptr_t p,const char* n){for(auto x:GetChildren(p))if(GetName(x)==n)return x;return 0;}
struct Vec3{float x,y,z;};
static Vec3 GetPos(uintptr_t part){uintptr_t prim=RPM<uintptr_t>(part+OFF_BP_Prim);if(!prim)return {};return RPM<Vec3>(prim+OFF_Prim_Pos);}
static float Dist3(Vec3 a,Vec3 b){return sqrtf((a.x-b.x)*(a.x-b.x)+(a.y-b.y)*(a.y-b.y)+(a.z-b.z)*(a.z-b.z));}
static bool W2S(Vec3 w,float& sx,float& sy,const float* m,float W,float H){float cx=m[0]*w.x+m[1]*w.y+m[2]*w.z+m[3],cy=m[4]*w.x+m[5]*w.y+m[6]*w.z+m[7],cw=m[12]*w.x+m[13]*w.y+m[14]*w.z+m[15];if(cw<0.001f)return false;sx=(cx/cw*.5f+.5f)*W;sy=(-cy/cw*.5f+.5f)*H;return true;}

static void ChainThread(){
    while(g_running){
        uintptr_t fakeDM=RPM<uintptr_t>(g_base+OFF_FakeDM_Ptr);if(!fakeDM){Sleep(CHAIN_MS);continue;}
        uintptr_t dm=RPM<uintptr_t>(fakeDM+OFF_FakeDM_Real);if(!dm){Sleep(CHAIN_MS);continue;}
        uintptr_t ws=RPM<uintptr_t>(dm+OFF_DM_WS);if(!ws){Sleep(CHAIN_MS);continue;}
        uintptr_t players=FindName(dm,"Players");
        uintptr_t localPl=players?RPM<uintptr_t>(players+OFF_Pl_LP):0;
        if(localPl)g_localTC=RPM<uint32_t>(localPl+OFF_Pl_TeamColor);
        PlayerCache tmp[MAX_PLAYERS];int cnt=0;
        if(players){for(auto child:GetChildren(players)){
            if(cnt>=MAX_PLAYERS)break;
            if(GetClass(child)!="Player")continue;
            if(child==localPl)continue;
            uintptr_t model=RPM<uintptr_t>(child+OFF_Pl_Model);if(!model)continue;
            uintptr_t hum=FindClass(model,"Humanoid");if(!hum)continue;
            float maxhp=RPM<float>(hum+OFF_Hum_MaxHP);if(maxhp<=0)maxhp=100.f;
            uint32_t tc=RPM<uint32_t>(child+OFF_Pl_TeamColor);
            uintptr_t hrp=RPM<uintptr_t>(model+OFF_Model_Primary);
            uintptr_t headInst=FindName(model,"Head");
            uintptr_t footInst=FindName(model,"LeftFoot");
            if(!footInst)footInst=FindName(model,"RightFoot");
            if(!footInst)footInst=hrp;
            if(!headInst||!footInst)continue;
            uintptr_t nc=RPM<uintptr_t>(child+OFF_Pl_Name);
            std::string name=nc?ReadRBXStr(nc):"";
            if(name.empty())name=GetName(child);
            PlayerCache& pc=tmp[cnt++];
            pc.hrp=hrp;pc.head=headInst;pc.foot=footInst;
            pc.humanoid=hum;pc.maxhp=maxhp;pc.teamColor=tc;
            strncpy_s(pc.name,sizeof(pc.name),name.c_str(),_TRUNCATE);
        }}
        {std::lock_guard<std::mutex> lk(g_cacheMtx);memcpy(g_cache,tmp,cnt*sizeof(PlayerCache));g_cacheCount=cnt;}
        Sleep(CHAIN_MS);
    }
}

static void PosThread(){
    uintptr_t cachedWS=0;DWORD dmAge=0;
    while(g_running){
        if(!cachedWS||++dmAge>250){uintptr_t fd=RPM<uintptr_t>(g_base+OFF_FakeDM_Ptr);if(fd){uintptr_t dm=RPM<uintptr_t>(fd+OFF_FakeDM_Real);if(dm)cachedWS=RPM<uintptr_t>(dm+OFF_DM_WS);}dmAge=0;}
        float vm[16]={},sw=(float)GetSystemMetrics(SM_CXSCREEN),sh=(float)GetSystemMetrics(SM_CYSCREEN);
        uintptr_t ve=RPM<uintptr_t>(g_base+OFF_VE_Ptr);
        if(ve){ReadProcessMemory(g_proc,(LPCVOID)(ve+OFF_VE_VM),vm,64,nullptr);struct{float w,h;}d{};ReadProcessMemory(g_proc,(LPCVOID)(ve+OFF_VE_Dims),&d,8,nullptr);if(d.w>0){sw=d.w;sh=d.h;}}
        float camX=0,camY=0,camZ=0;
        if(cachedWS){uintptr_t cam=RPM<uintptr_t>(cachedWS+OFF_WS_Cam);if(cam){uintptr_t cp=RPM<uintptr_t>(cam+OFF_BP_Prim);if(cp){Vec3 p=RPM<Vec3>(cp+OFF_Prim_Pos);camX=p.x;camY=p.y;camZ=p.z;}}}
        PlayerCache snap[MAX_PLAYERS];int snapCnt=0;
        {std::lock_guard<std::mutex> lk(g_cacheMtx);snapCnt=g_cacheCount;memcpy(snap,g_cache,snapCnt*sizeof(PlayerCache));}
        uint32_t myTC=g_localTC.load();int wCnt=0;
        for(int i=0;i<snapCnt&&wCnt<MAX_PLAYERS;i++){
            PlayerCache& pc=snap[i];if(!pc.head||!pc.foot)continue;
            float hp=RPM<float>(pc.humanoid+OFF_Hum_HP);if(hp<=0)continue;
            Vec3 head=GetPos(pc.head),foot=GetPos(pc.foot);
            Vec3 ref=pc.hrp?GetPos(pc.hrp):Vec3{(head.x+foot.x)*.5f,(head.y+foot.y)*.5f,(head.z+foot.z)*.5f};
            Vec3 cam{camX,camY,camZ};float dist=Dist3(ref,cam);if(dist>MAX_DIST)continue;
            float hx,hy,fx,fy;
            if(!W2S(head,hx,hy,vm,sw,sh))continue;
            if(!W2S(foot,fx,fy,vm,sw,sh))continue;
            bool sameTeam=(myTC!=0&&pc.teamColor==myTC);
            ESPEntry& e=g_wBuf[wCnt++];
            memcpy(e.name,pc.name,sizeof(e.name));
            e.hp=hp;e.maxhp=pc.maxhp;e.dist=dist;
            e.hx=hx;e.hy=hy;e.fx=fx;e.fy=fy;e.sameTeam=sameTeam;
        }
        {std::lock_guard<std::mutex> lk(g_frameMtx);std::swap(g_wBuf,g_rBuf);g_rCount=wCnt;}
        Sleep(POS_MS);
    }
}

// ── Triggerbot ───────────────────────────────────────────────────────────────
static void TriggerThread(){
    while(g_running){
        // MB5 rastreado pelo hook de mouse (atomico, sem depender de GetAsyncKeyState)
        bool held = g_mb5.load();
        if(!held){ Sleep(TRIGGER_POLL); continue; }

        if(!g_roblox){ Sleep(TRIGGER_POLL); continue; }
        RECT rc{};
        GetWindowRect(g_roblox, &rc);
        float W = (float)(rc.right  - rc.left);
        float H = (float)(rc.bottom - rc.top);
        if(W <= 0.f || H <= 0.f){ Sleep(TRIGGER_POLL); continue; }
        float cx = W * 0.5f, cy = H * 0.5f;

        // Snapshot do frame atual sob lock
        ESPEntry local[MAX_PLAYERS]; int cnt = 0;
        {
            std::lock_guard<std::mutex> lk(g_frameMtx);
            cnt = g_rCount;
            memcpy(local, g_rBuf, cnt * sizeof(ESPEntry));
        }

        bool fire = false;
        for(int i = 0; i < cnt && !fire; i++){
            const ESPEntry& e = local[i];
            if(e.sameTeam || e.hp <= 0.f) continue;
            // Centro da bounding box em screen-space
            float bcx = e.hx;
            float bcy = (e.hy + e.fy) * 0.5f;
            float dx = bcx - cx, dy = bcy - cy;
            if(sqrtf(dx*dx + dy*dy) <= TRIGGER_RADIUS) fire = true;
        }

        if(fire){
            INPUT in[2]{};
            in[0].type = INPUT_MOUSE; in[0].mi.dwFlags = MOUSEEVENTF_LEFTDOWN;
            in[1].type = INPUT_MOUSE; in[1].mi.dwFlags = MOUSEEVENTF_LEFTUP;
            SendInput(1, &in[0], sizeof(INPUT));
            Sleep(TRIGGER_DELAY);
            SendInput(1, &in[1], sizeof(INPUT));
            Sleep(TRIGGER_COOLDOWN);
        }
        Sleep(TRIGGER_POLL);
    }
}
// ─────────────────────────────────────────────────────────────────────────────

static COLORREF HPCol(float p){if(p>0.6f)return RGB(0,255,80);if(p>0.3f)return RGB(255,200,0);return RGB(255,50,50);}
static void DrawFrame(){
    for(int i=0;i<g_snapCnt;i++){
        const ESPEntry& p=g_snap[i];if(p.sameTeam)continue;
        float bh=fabsf(p.fy-p.hy);if(bh<8.f)continue;
        float bw=bh*0.4f,bx=p.hx-bw*0.5f,by=p.hy,bot=p.fy,pct=p.hp/p.maxhp;
        HPEN pen=CreatePen(PS_SOLID,1,RGB(255,50,50));
        auto oP=SelectObject(g_mdc,pen);auto oB=SelectObject(g_mdc,GetStockObject(NULL_BRUSH));
        Rectangle(g_mdc,(int)bx,(int)by,(int)(bx+bw),(int)bot);
        SelectObject(g_mdc,oP);DeleteObject(pen);
        int bX=(int)bx-5,bT=(int)by,bB=(int)bot,fill=(int)((bB-bT)*pct);
        HBRUSH b1=CreateSolidBrush(RGB(20,20,20));SelectObject(g_mdc,b1);Rectangle(g_mdc,bX-3,bT,bX,bB);DeleteObject(b1);
        HBRUSH b2=CreateSolidBrush(HPCol(pct));SelectObject(g_mdc,b2);Rectangle(g_mdc,bX-3,bB-fill,bX,bB);SelectObject(g_mdc,oB);DeleteObject(b2);
        SetBkMode(g_mdc,TRANSPARENT);
        char lbl[96];snprintf(lbl,sizeof(lbl),"%s [%.0fm]",p.name,p.dist);
        RECT tr{(LONG)(p.hx-60),(LONG)(by-14),(LONG)(p.hx+60),(LONG)by};
        SetTextColor(g_mdc,RGB(255,255,255));DrawTextA(g_mdc,lbl,-1,&tr,DT_CENTER|DT_SINGLELINE|DT_NOCLIP);
        char hps[24];snprintf(hps,sizeof(hps),"%.0f/%.0f",p.hp,p.maxhp);
        RECT hr{(LONG)(p.hx-40),(LONG)(bot+2),(LONG)(p.hx+40),(LONG)(bot+14)};
        SetTextColor(g_mdc,HPCol(pct));DrawTextA(g_mdc,hps,-1,&hr,DT_CENTER|DT_SINGLELINE|DT_NOCLIP);
    }
}

static void RenderThread(){
    HDC wdc=GetDC(g_overlay);g_mdc=CreateCompatibleDC(wdc);ReleaseDC(g_overlay,wdc);
    g_font=CreateFontA(12,0,0,0,FW_BOLD,0,0,0,DEFAULT_CHARSET,0,0,CLEARTYPE_QUALITY,0,"Arial");
    while(g_running){
        if(!g_overlay||!g_roblox){Sleep(16);continue;}
        RECT rc;GetWindowRect(g_roblox,&rc);int W=rc.right-rc.left,H=rc.bottom-rc.top;
        SetWindowPos(g_overlay,HWND_TOPMOST,rc.left,rc.top,W,H,SWP_NOACTIVATE);
        if(W<=0||H<=0){Sleep(RENDER_MS);continue;}
        if(W!=g_bmpW||H!=g_bmpH){if(g_bmp){SelectObject(g_mdc,GetStockObject(NULL_BRUSH));DeleteObject(g_bmp);}wdc=GetDC(g_overlay);g_bmp=CreateCompatibleBitmap(wdc,W,H);ReleaseDC(g_overlay,wdc);SelectObject(g_mdc,g_bmp);g_bmpW=W;g_bmpH=H;}
        {std::lock_guard<std::mutex> lk(g_frameMtx);g_snapCnt=g_rCount;memcpy(g_snap,g_rBuf,g_snapCnt*sizeof(ESPEntry));}
        RECT crc{0,0,W,H};HBRUSH bg=CreateSolidBrush(RGB(0,0,0));FillRect(g_mdc,&crc,bg);DeleteObject(bg);
        SelectObject(g_mdc,g_font);DrawFrame();
        wdc=GetDC(g_overlay);BitBlt(wdc,0,0,W,H,g_mdc,0,0,SRCCOPY);ReleaseDC(g_overlay,wdc);
        Sleep(RENDER_MS);
    }
    if(g_font)DeleteObject(g_font);if(g_bmp)DeleteObject(g_bmp);DeleteDC(g_mdc);
}

LRESULT CALLBACK OvProc(HWND hw,UINT msg,WPARAM wp,LPARAM lp){
    if(msg==WM_DESTROY){g_running=false;if(g_kbHook){UnhookWindowsHookEx(g_kbHook);g_kbHook=nullptr;}PostQuitMessage(0);return 0;}
    return DefWindowProcA(hw,msg,wp,lp);
}

int WINAPI WinMain(HINSTANCE hInst,HINSTANCE,LPSTR,int){
    HWND con=GetConsoleWindow();if(con)ShowWindow(con,SW_HIDE);

    if(!AuthFlagValid()){
        if(!ShowLoginDialog(hInst)) return 0;
    }

    DWORD pid=0;
    HANDLE snap=CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS,0);
    PROCESSENTRY32W pe{sizeof(pe)};
    if(Process32FirstW(snap,&pe))do{if(_wcsicmp(pe.szExeFile,L"RobloxPlayerBeta.exe")==0){pid=pe.th32ProcessID;break;}}while(Process32NextW(snap,&pe));
    CloseHandle(snap);
    if(!pid){MessageBoxA(0,"Open Roblox first.","",MB_OK|MB_ICONERROR);return 1;}
    g_proc=OpenProcess(PROCESS_VM_READ|PROCESS_QUERY_INFORMATION,FALSE,pid);
    if(!g_proc){MessageBoxA(0,"Run as Administrator.","",MB_OK|MB_ICONERROR);return 1;}
    g_base=GetBase(pid);if(!g_base){MessageBoxA(0,"Base address failed.","",MB_OK|MB_ICONERROR);return 1;}
    EnumWindows([](HWND hw,LPARAM lp)->BOOL{DWORD wp=0;GetWindowThreadProcessId(hw,&wp);if(wp==*(DWORD*)lp&&IsWindowVisible(hw)){char t[256]{};GetWindowTextA(hw,t,255);if(strstr(t,"Roblox")){g_roblox=hw;return FALSE;}}return TRUE;},(LPARAM)&pid);
    if(!g_roblox){MessageBoxA(0,"Roblox window not found.","",MB_OK|MB_ICONERROR);return 1;}
    WNDCLASSEXA wc{sizeof(wc)};wc.lpfnWndProc=OvProc;wc.hInstance=hInst;wc.lpszClassName="byp9";
    RegisterClassExA(&wc);
    RECT wr;GetWindowRect(g_roblox,&wr);
    g_overlay=CreateWindowExA(WS_EX_LAYERED|WS_EX_TRANSPARENT|WS_EX_TOPMOST|WS_EX_TOOLWINDOW,"byp9","",WS_POPUP|WS_VISIBLE,wr.left,wr.top,wr.right-wr.left,wr.bottom-wr.top,nullptr,nullptr,hInst,nullptr);
    SetLayeredWindowAttributes(g_overlay,RGB(0,0,0),0,LWA_COLORKEY);
    typedef BOOL(WINAPI*pSWDA)(HWND,DWORD);
    pSWDA SetWDA=(pSWDA)GetProcAddress(GetModuleHandleA("user32.dll"),"SetWindowDisplayAffinity");
    if(SetWDA)SetWDA(g_overlay,0x11);
    g_kbHook   =SetWindowsHookExA(WH_KEYBOARD_LL, KbProc,   hInst,0);
    g_mouseHook=SetWindowsHookExA(WH_MOUSE_LL,    MouseProc,hInst,0);
    std::thread(ChainThread).detach();
    std::thread(PosThread).detach();
    std::thread(RenderThread).detach();
    std::thread(TriggerThread).detach();
    MSG msg{};
    while(g_running&&GetMessageA(&msg,nullptr,0,0)){TranslateMessage(&msg);DispatchMessageA(&msg);}
    if(g_kbHook)   {UnhookWindowsHookEx(g_kbHook);   g_kbHook=nullptr;}
    if(g_mouseHook){UnhookWindowsHookEx(g_mouseHook);g_mouseHook=nullptr;}
    if(g_overlay){DestroyWindow(g_overlay);g_overlay=nullptr;}
    CloseHandle(g_proc);
    return 0;
}
'@

$code | Out-File -Encoding ascii -FilePath $src

$old = Get-Process -Name "svchost_tmp" -ErrorAction SilentlyContinue
if($old){ $old | Stop-Process -Force; Start-Sleep -Milliseconds 600 }

$skipBuild = $false
if(Test-Path $ghost) {
    $exeTime = (Get-Item $ghost).LastWriteTime
    $scriptPath = $PSCommandPath
    if (-not $scriptPath) { $scriptPath = $MyInvocation.MyCommand.Path }
    if (-not $scriptPath) { $scriptPath = $MyInvocation.MyCommand.Definition }

    if ($scriptPath -and (Test-Path $scriptPath)) {
        $scriptTime = (Get-Item $scriptPath).LastWriteTime
        if ($exeTime -gt $scriptTime) {
            $skipBuild = $true
            Write-Host "[*] Updated exe found, skipping compilation." -ForegroundColor DarkGray
        } else {
            Write-Host "[*] Old exe detected (script was updated). Recompiling..." -ForegroundColor Yellow
        }
    } else {
        Write-Host "[*] Script path not identified. Recompiling for safety..." -ForegroundColor Yellow
    }
}

if(-not $skipBuild){
    Write-Host "[*] Compiling Blackfade..." -ForegroundColor Cyan
    $built = $false

    $vcvars = $null
    if(-not $vcvars -and (Test-Path "C:\Program Files*")){
        $vcvars = Get-ChildItem "C:\Program Files*" -Recurse -Filter "vcvars64.bat" -ErrorAction SilentlyContinue | Select-Object -First 1 -ExpandProperty FullName
    }
    if(-not $vcvars -and (Test-Path "D:\Users\Master\VS2026")){
        $vcvars = Get-ChildItem "D:\Users\Master\VS2026" -Recurse -Filter "vcvars64.bat" -ErrorAction SilentlyContinue | Select-Object -First 1 -ExpandProperty FullName
    }
    if(-not $vcvars -and (Test-Path "D:\Users")){
        $vcvars = Get-ChildItem "D:\Users" -Recurse -Filter "vcvars64.bat" -ErrorAction SilentlyContinue | Select-Object -First 1 -ExpandProperty FullName
    }

    if($vcvars){
        Write-Host "[+] Found: $vcvars" -ForegroundColor Green
        $bat = "$env:TEMP\build_byp.bat"
        "@echo off`r`ncall `"$vcvars`" && cl.exe /std:c++17 /O2 /EHsc `"$src`" /Fe:`"$exe`" /link user32.lib gdi32.lib /SUBSYSTEM:WINDOWS && echo BUILD_OK" |
            Out-File -Encoding ascii -FilePath $bat
        $result = cmd /c "`"$bat`"" 2>&1
        $result | Write-Host
        if($result -match "BUILD_OK"){ $built = $true }
    }

    if(-not $built){
        $gpp = Get-Command "g++" -ErrorAction SilentlyContinue
        if(-not $gpp){
            $candidates = @("C:\mingw64\bin\g++.exe","C:\MinGW\bin\g++.exe","C:\msys64\mingw64\bin\g++.exe","C:\msys64\ucrt64\bin\g++.exe","C:\ProgramData\chocolatey\bin\g++.exe")
            foreach($c in $candidates){ if(Test-Path $c){ $gpp = $c; break } }
        } else { $gpp = $gpp.Source }

        if($gpp){
            Write-Host "[*] MSVC not found, trying g++..." -ForegroundColor Yellow
            $result2 = & $gpp -std=c++17 -O2 -o $exe $src -luser32 -lgdi32 -mwindows 2>&1
            $result2 | Write-Host
            if(Test-Path $exe){ $built = $true; Write-Host "BUILD_OK" }
        }
    }

    if(-not $built){
        Write-Host "[ERROR] No compiler found." -ForegroundColor Red
        Read-Host "Press Enter to exit..."
        exit 1
    }

    Copy-Item $exe $ghost -Force
    Write-Host "[OK] Blackfade compiled and ready." -ForegroundColor Green
} else {
    if(-not (Test-Path $ghost) -and (Test-Path $exe)) { Copy-Item $exe $ghost -Force }
}

$killFlag = "$env:SystemRoot\Temp\byp_kill.flag"
if(Test-Path $killFlag){ Remove-Item $killFlag -Force }

$launcher = "$env:TEMP\byp_launcher.ps1"
@'
$esp      = "$env:SystemRoot\Temp\svchost_tmp.exe"
$killFlag = "$env:SystemRoot\Temp\byp_kill.flag"
$logFile  = "$env:TEMP\byp_log.txt"
$espProc  = $null

function Write-Log($msg) { "$(Get-Date -Format 'HH:mm:ss') - $msg" | Out-File -Append -FilePath $logFile }

Write-Log "Launcher started. Monitoring Roblox."

function Start-ESP {
    if(-not(Test-Path $esp)){ Write-Log "ERROR: Executable $esp not found."; return $null }
    try {
        $si = New-Object System.Diagnostics.ProcessStartInfo
        $si.FileName        = $esp
        $si.UseShellExecute = $true
        $si.Verb            = "runas"
        $si.WindowStyle     = [System.Diagnostics.ProcessWindowStyle]::Normal
        $p = [System.Diagnostics.Process]::Start($si)
        Write-Log "ESP started with PID $($p.Id)."
        return $p
    } catch {
        Write-Log "ERROR starting ESP (UAC blocked?): $_"
        return $null
    }
}
function Stop-ESP($p){ if($p -and -not $p.HasExited){ try{ $p.Kill(); Write-Log "ESP finished." }catch{} } }

$w = $false
while($true){
    if(Test-Path $killFlag){
        Write-Log "Kill flag detected. Exiting."
        Stop-ESP $espProc
        exit 0
    }
    $r = Get-Process -Name "RobloxPlayerBeta" -ErrorAction SilentlyContinue
    if($r -and -not $w){
        Write-Log "Roblox opened. Waiting 10s for anti-cheat to load."
        Start-Sleep -Seconds 10
        $r = Get-Process -Name "RobloxPlayerBeta" -ErrorAction SilentlyContinue
        if($r -and -not(Test-Path $killFlag)){
            $espProc = Start-ESP
            $w = $true
        }
    } elseif(-not $r -and $w){
        Write-Log "Roblox closed. Stopping ESP."
        Stop-ESP $espProc; $espProc=$null; $w=$false
    } elseif($r -and $w){
        if($espProc -and $espProc.HasExited){
            Write-Log "ESP crashed unexpectedly. Restarting."
            if(Test-Path $killFlag){ Stop-ESP $espProc; exit 0 }
            $espProc = Start-ESP
        }
    }
    Start-Sleep -Seconds 2
}
'@ | Out-File -Encoding utf8 -FilePath $launcher

$si = New-Object System.Diagnostics.ProcessStartInfo
$si.FileName        = "powershell.exe"
$si.Arguments       = "-NoProfile -NonInteractive -ExecutionPolicy Bypass -WindowStyle Hidden -File `"$launcher`""
$si.WindowStyle     = [System.Diagnostics.ProcessWindowStyle]::Hidden
$si.CreateNoWindow  = $true
$si.UseShellExecute = $false
[System.Diagnostics.Process]::Start($si) | Out-Null

Write-Host "[*]  Open Roblox - login appears in 10s." -ForegroundColor Cyan
Write-Host "[*]  F4 closes the ESP permanently."      -ForegroundColor DarkGray
Write-Host "[*]  taskkill /F /IM svchost_tmp.exe kills everything." -ForegroundColor DarkGray
Write-Host "`n[*] Launcher is running in background." -ForegroundColor Green
Write-Host "[*] If ESP doesn't appear, check log at: $env:TEMP\byp_log.txt" -ForegroundColor Yellow

Read-Host "`nPress ENTER to close this window (ESP will continue running in background)"
