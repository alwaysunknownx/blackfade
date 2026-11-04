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

constexpr float MAX_DIST    = 1000.f;
constexpr int   MAX_PLAYERS = 100;
constexpr int   CHAIN_MS    = 1000;
constexpr int   POS_MS      = 8;
constexpr int   RENDER_MS   = 8;

static const wchar_t* KILL_FLAG = L"C:\\Windows\\Temp\\byp_kill.flag";
static const wchar_t* AUTH_FLAG = L"C:\\Windows\\Temp\\byp_auth.flag";

static void WriteKillFlag(){
    HANDLE h=CreateFileW(KILL_FLAG,GENERIC_WRITE,0,nullptr,CREATE_ALWAYS,FILE_ATTRIBUTE_NORMAL,nullptr);
    if(h!=INVALID_HANDLE_VALUE){DWORD w=0;WriteFile(h,"1",1,&w,nullptr);CloseHandle(h);}
    // apaga auth para exigir login na proxima abertura
    DeleteFileW(AUTH_FLAG);
}

// retorna o timestamp de boot em unidades de 100ns (FILETIME epoch)
static ULONGLONG GetBootEpoch(){
    FILETIME ft; GetSystemTimeAsFileTime(&ft);
    ULARGE_INTEGER now; now.LowPart=ft.dwLowDateTime; now.HighPart=ft.dwHighDateTime;
    ULONGLONG uptimeHns = GetTickCount64() * 10000ULL;
    return now.QuadPart - uptimeHns;
}

static void WriteAuthFlag(){
    ULONGLONG boot = GetBootEpoch();
    HANDLE h=CreateFileW(AUTH_FLAG,GENERIC_WRITE,0,nullptr,CREATE_ALWAYS,FILE_ATTRIBUTE_NORMAL,nullptr);
    if(h!=INVALID_HANDLE_VALUE){DWORD w=0;WriteFile(h,&boot,sizeof(boot),&w,nullptr);CloseHandle(h);}
}

// true = auth flag valida para este boot (pode pular login)
static bool AuthFlagValid(){
    HANDLE h=CreateFileW(AUTH_FLAG,GENERIC_READ,FILE_SHARE_READ,nullptr,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,nullptr);
    if(h==INVALID_HANDLE_VALUE) return false;
    ULONGLONG stored=0; DWORD r=0;
    ReadFile(h,&stored,sizeof(stored),&r,nullptr);
    CloseHandle(h);
    if(r!=sizeof(stored)) return false;
    ULONGLONG boot=GetBootEpoch();
    // tolera 30s de drift no calculo de boot
    ULONGLONG diff = (boot>stored)?(boot-stored):(stored-boot);
    return diff < 300000000ULL; // 30s em 100ns
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
static HDC g_mdc=nullptr;
static HBITMAP g_bmp=nullptr;
static int g_bmpW=0,g_bmpH=0;
static HFONT g_font=nullptr;
static ESPEntry g_snap[MAX_PLAYERS];
static int g_snapCnt=0;

// ── Login ────────────────────────────────────────────────────────────────────
static bool      g_loginOK   = false;
static HINSTANCE g_loginInst = nullptr;
static HWND      g_hUser     = nullptr;
static HWND      g_hPass     = nullptr;

static LRESULT CALLBACK LoginWndProc(HWND hw,UINT msg,WPARAM wp,LPARAM lp){
    switch(msg){
    case WM_CREATE:{
        int x=20,y=20,fw=200,fh=22;
        CreateWindowExW(0,L"STATIC",L"Utilizador:",WS_CHILD|WS_VISIBLE,x,y,fw,fh,hw,nullptr,g_loginInst,nullptr);
        g_hUser=CreateWindowExW(WS_EX_CLIENTEDGE,L"EDIT",L"",WS_CHILD|WS_VISIBLE|WS_TABSTOP|ES_AUTOHSCROLL,x,y+22,fw,fh,hw,(HMENU)101,g_loginInst,nullptr);
        CreateWindowExW(0,L"STATIC",L"Senha:",WS_CHILD|WS_VISIBLE,x,y+54,fw,fh,hw,nullptr,g_loginInst,nullptr);
        g_hPass=CreateWindowExW(WS_EX_CLIENTEDGE,L"EDIT",L"",WS_CHILD|WS_VISIBLE|WS_TABSTOP|ES_PASSWORD|ES_AUTOHSCROLL,x,y+76,fw,fh,hw,(HMENU)102,g_loginInst,nullptr);
        CreateWindowExW(0,L"BUTTON",L"Entrar",WS_CHILD|WS_VISIBLE|WS_TABSTOP|BS_DEFPUSHBUTTON,x,y+112,90,28,hw,(HMENU)103,g_loginInst,nullptr);
        CreateWindowExW(0,L"BUTTON",L"Cancelar",WS_CHILD|WS_VISIBLE|WS_TABSTOP,x+110,y+112,90,28,hw,(HMENU)104,g_loginInst,nullptr);
        SetFocus(g_hUser);
        return 0;
    }
    case WM_COMMAND:{
        WORD id=LOWORD(wp);
        if(id==103){
            char u[64]{},p[64]{};
            GetWindowTextA(g_hUser,u,sizeof(u));
            GetWindowTextA(g_hPass,p,sizeof(p));
            if(strcmp(u,"Nightmare")==0&&strcmp(p,"nightshadegoat")==0){
                g_loginOK=true;
                WriteAuthFlag();  // persiste sessao
                DestroyWindow(hw);
            } else {
                MessageBoxA(hw,"Credenciais invalidas.","Acesso negado",MB_OK|MB_ICONERROR);
                SetWindowTextA(g_hPass,"");
                SetFocus(g_hPass);
            }
            return 0;
        }
        if(id==104){DestroyWindow(hw);return 0;}
        break;
    }
    case WM_DESTROY:
        PostQuitMessage(0);
        return 0;
    }
    return DefWindowProcW(hw,msg,wp,lp);
}

static bool ShowLoginDialog(HINSTANCE hInst){
    g_loginInst=hInst;
    static const wchar_t* CLS=L"NightmareLogin";
    WNDCLASSEXW wc{sizeof(wc)};
    wc.lpfnWndProc=LoginWndProc;
    wc.hInstance=hInst;
    wc.hCursor=LoadCursor(nullptr,IDC_ARROW);
    wc.hbrBackground=(HBRUSH)(COLOR_BTNFACE+1);
    wc.lpszClassName=CLS;
    RegisterClassExW(&wc);
    int sw=GetSystemMetrics(SM_CXSCREEN),sh=GetSystemMetrics(SM_CYSCREEN);
    int W=260,H=210;
    HWND dlg=CreateWindowExW(WS_EX_TOPMOST|WS_EX_DLGMODALFRAME,CLS,
        L"Nightmare - Login",WS_OVERLAPPED|WS_CAPTION|WS_SYSMENU,
        (sw-W)/2,(sh-H)/2,W,H,nullptr,nullptr,hInst,nullptr);
    if(!dlg){UnregisterClassW(CLS,hInst);return false;}
    ShowWindow(dlg,SW_SHOW);
    UpdateWindow(dlg);
    MSG m{};
    while(GetMessageW(&m,nullptr,0,0)){
        if(!IsDialogMessageW(dlg,&m)){TranslateMessage(&m);DispatchMessageW(&m);}
    }
    UnregisterClassW(CLS,hInst);
    return g_loginOK;
}
// ─────────────────────────────────────────────────────────────────────────────

static LRESULT CALLBACK KbProc(int code,WPARAM wp,LPARAM lp){
    if(code==HC_ACTION&&wp==WM_KEYDOWN){
        KBDLLHOOKSTRUCT* kb=(KBDLLHOOKSTRUCT*)lp;
        if(kb->vkCode==VK_END){
            WriteKillFlag();
            g_running=false;
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

    // gate de login — pula se ja autenticado neste boot
    if(!AuthFlagValid()){
        if(!ShowLoginDialog(hInst)) return 0;
    }

    DWORD pid=0;
    HANDLE snap=CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS,0);
    PROCESSENTRY32W pe{sizeof(pe)};
    if(Process32FirstW(snap,&pe))do{if(_wcsicmp(pe.szExeFile,L"RobloxPlayerBeta.exe")==0){pid=pe.th32ProcessID;break;}}while(Process32NextW(snap,&pe));
    CloseHandle(snap);
    if(!pid){MessageBoxA(0,"Abra o Roblox primeiro.","",MB_OK|MB_ICONERROR);return 1;}
    g_proc=OpenProcess(PROCESS_VM_READ|PROCESS_QUERY_INFORMATION,FALSE,pid);
    if(!g_proc){MessageBoxA(0,"Rode como Administrador.","",MB_OK|MB_ICONERROR);return 1;}
    g_base=GetBase(pid);if(!g_base){MessageBoxA(0,"Base address falhou.","",MB_OK|MB_ICONERROR);return 1;}
    EnumWindows([](HWND hw,LPARAM lp)->BOOL{DWORD wp=0;GetWindowThreadProcessId(hw,&wp);if(wp==*(DWORD*)lp&&IsWindowVisible(hw)){char t[256]{};GetWindowTextA(hw,t,255);if(strstr(t,"Roblox")){g_roblox=hw;return FALSE;}}return TRUE;},(LPARAM)&pid);
    if(!g_roblox){MessageBoxA(0,"Janela do Roblox nao encontrada.","",MB_OK|MB_ICONERROR);return 1;}
    WNDCLASSEXA wc{sizeof(wc)};wc.lpfnWndProc=OvProc;wc.hInstance=hInst;wc.lpszClassName="byp9";
    RegisterClassExA(&wc);
    RECT wr;GetWindowRect(g_roblox,&wr);
    g_overlay=CreateWindowExA(WS_EX_LAYERED|WS_EX_TRANSPARENT|WS_EX_TOPMOST|WS_EX_TOOLWINDOW,"byp9","",WS_POPUP|WS_VISIBLE,wr.left,wr.top,wr.right-wr.left,wr.bottom-wr.top,nullptr,nullptr,hInst,nullptr);
    SetLayeredWindowAttributes(g_overlay,RGB(0,0,0),0,LWA_COLORKEY);
    typedef BOOL(WINAPI*pSWDA)(HWND,DWORD);
    pSWDA SetWDA=(pSWDA)GetProcAddress(GetModuleHandleA("user32.dll"),"SetWindowDisplayAffinity");
    if(SetWDA)SetWDA(g_overlay,0x11);
    g_kbHook=SetWindowsHookExA(WH_KEYBOARD_LL,KbProc,hInst,0);
    std::thread(ChainThread).detach();
    std::thread(PosThread).detach();
    std::thread(RenderThread).detach();
    MSG msg{};
    while(g_running&&GetMessageA(&msg,nullptr,0,0)){TranslateMessage(&msg);DispatchMessageA(&msg);}
    if(g_kbHook){UnhookWindowsHookEx(g_kbHook);g_kbHook=nullptr;}
    if(g_overlay){DestroyWindow(g_overlay);g_overlay=nullptr;}
    CloseHandle(g_proc);
    return 0;
}
'@

$code | Out-File -Encoding ascii -FilePath $src

# ── Mata instancia anterior antes de qualquer copia ───────────────────────────
$old = Get-Process -Name "svchost_tmp" -ErrorAction SilentlyContinue
if($old){ $old | Stop-Process -Force; Start-Sleep -Milliseconds 600 }

# ── Se o exe ja existe (copiado do PC principal) pula compilacao ──────────────
if(Test-Path $ghost){
    Write-Host "[*] Exe encontrado, pulando compilacao." -ForegroundColor DarkGray
} else {
    Write-Host "[*] Compilando Bypassier v9..." -ForegroundColor Cyan

    $built = $false

    # --- tentativa 1: MSVC ---
    $vcvars = Get-ChildItem "C:\Program Files*\Microsoft Visual Studio" `
        -Recurse -Filter "vcvars64.bat" -ErrorAction SilentlyContinue |
        Select-Object -First 1 -ExpandProperty FullName

    if($vcvars){
        $bat = "$env:TEMP\build_byp.bat"
        "@echo off`r`ncall `"$vcvars`" && cl.exe /std:c++17 /O2 /EHsc `"$src`" /Fe:`"$exe`" /link user32.lib gdi32.lib /SUBSYSTEM:WINDOWS && echo BUILD_OK" |
            Out-File -Encoding ascii -FilePath $bat
        $result = cmd /c "`"$bat`"" 2>&1
        $result | Write-Host
        if($result -match "BUILD_OK"){ $built = $true }
    }

    # --- tentativa 2: MinGW / g++ ---
    if(-not $built){
        $gpp = Get-Command "g++" -ErrorAction SilentlyContinue
        if(-not $gpp){
            # tenta paths comuns do MinGW
            $candidates = @(
                "C:\mingw64\bin\g++.exe",
                "C:\MinGW\bin\g++.exe",
                "C:\msys64\mingw64\bin\g++.exe",
                "C:\msys64\ucrt64\bin\g++.exe",
                "C:\ProgramData\chocolatey\bin\g++.exe"
            )
            foreach($c in $candidates){ if(Test-Path $c){ $gpp = $c; break } }
        } else { $gpp = $gpp.Source }

        if($gpp){
            Write-Host "[*] MSVC nao encontrado, tentando g++..." -ForegroundColor Yellow
            $result2 = & $gpp -std=c++17 -O2 -o $exe $src `
                -luser32 -lgdi32 -mwindows 2>&1
            $result2 | Write-Host
            if(Test-Path $exe){ $built = $true; Write-Host "BUILD_OK" }
        }
    }

    if(-not $built){
        Write-Host "" -ForegroundColor Red
        Write-Host "[ERRO] Nenhum compilador encontrado." -ForegroundColor Red
        Write-Host "       Opcoes:" -ForegroundColor Yellow
        Write-Host "       1) Instale Visual Studio com C++ (recomendado)" -ForegroundColor Yellow
        Write-Host "       2) Instale MinGW: winget install MinGW.MinGW" -ForegroundColor Yellow
        Write-Host "       3) Copie o svchost_tmp.exe do PC onde ja compilou para:" -ForegroundColor Yellow
        Write-Host "          $ghost" -ForegroundColor Cyan
        Write-Host "          e rode o script novamente." -ForegroundColor Yellow
        exit 1
    }

    Copy-Item $exe $ghost -Force
    Write-Host "[OK] Bypassier v9 compilado e pronto." -ForegroundColor Green
}

$killFlag = "$env:SystemRoot\Temp\byp_kill.flag"
if(Test-Path $killFlag){ Remove-Item $killFlag -Force }

$launcher = "$env:TEMP\byp_launcher.ps1"
@'
$esp      = "$env:SystemRoot\Temp\svchost_tmp.exe"
$killFlag = "$env:SystemRoot\Temp\byp_kill.flag"
$espProc  = $null

function Start-ESP {
    if(-not(Test-Path $esp)){ return $null }
    $si = New-Object System.Diagnostics.ProcessStartInfo
    $si.FileName        = $esp
    $si.UseShellExecute = $true
    $si.Verb            = "runas"
    $si.WindowStyle     = [System.Diagnostics.ProcessWindowStyle]::Normal
    return [System.Diagnostics.Process]::Start($si)
}
function Stop-ESP($p){ if($p -and -not $p.HasExited){ try{ $p.Kill() }catch{} } }

$w = $false
while($true){
    if(Test-Path $killFlag){
        Stop-ESP $espProc
        exit 0
    }
    $r = Get-Process -Name "RobloxPlayerBeta" -ErrorAction SilentlyContinue
    if($r -and -not $w){
        Start-Sleep -Seconds 10
        $r = Get-Process -Name "RobloxPlayerBeta" -ErrorAction SilentlyContinue
        if($r -and -not(Test-Path $killFlag)){
            $espProc = Start-ESP
            $w = $true
        }
    } elseif(-not $r -and $w){
        Stop-ESP $espProc; $espProc=$null; $w=$false
    } elseif($r -and $w){
        if($espProc -and $espProc.HasExited){
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

Write-Host "[*]  Abre o Roblox - login aparece em 10s." -ForegroundColor Cyan
Write-Host "[*]  END fecha o ESP permanentemente."      -ForegroundColor DarkGray
Write-Host "[*]  taskkill /F /IM svchost_tmp.exe mata tudo." -ForegroundColor DarkGray
