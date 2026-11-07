/* bsaim v2 - BloodStrike aim assist (root, screen-scan) */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <dirent.h>
#include <linux/input.h>
#include <linux/uinput.h>
#include <sys/ioctl.h>
#include <sys/wait.h>

#define PKG "com.netease.newspike"
#define CELL 12
#define MAXCELLS 9216

static int LOGFD = -1;
static void lg(const char *f, ...) {
    if (LOGFD < 0) return;
    va_list a; va_start(a, f); vdprintf(LOGFD, f, a); va_end(a);
}

static struct {
    int acquire_r, track_r, fov_limit, min_px, max_px, lock_frames, lost_ms, stride;
    int smooth, gain, predict, deadzone, max_step, hz;
    int rmin, gmax, bmax, rg, rb;
} C = {150, 300, 380, 45, 12000, 2, 450, 2, 62, 120, 60, 2, 170, 18,
       155, 90, 90, 60, 60};

static unsigned char *fb = NULL;
static size_t fbcap = 0;
static int vfd = -1, kfd = -1, SW = 0, SH = 0;
static volatile int run = 1, enabled = 1;
static int tid = 100;

static int cnt[MAXCELLS];
static unsigned char vis[MAXCELLS];
static int stack_[MAXCELLS];

static void onsig(int s) { (void)s; run = 0; }

static void preset(const char *p) {
    if (!strcmp(p, "magenta")) { C.rmin = 140; C.gmax = 90; C.bmax = 200; C.rg = 55; C.rb = 0; }
    else if (!strcmp(p, "yellow")) { C.rmin = 165; C.gmax = 255; C.bmax = 110; C.rg = 25; C.rb = 65; }
    else if (!strcmp(p, "cyan")) { C.rmin = 30; C.gmax = 255; C.bmax = 255; C.rg = 0; C.rb = 0; }
    else if (!strcmp(p, "green")) { C.rmin = 90; C.gmax = 255; C.bmax = 140; C.rg = 0; C.rb = 40; }
}

static void cfg(const char *p) {
    FILE *f = fopen(p, "r");
    if (!f) return;
    char l[256], key[64], val[64];
    while (fgets(l, sizeof l, f)) {
        char *s = l; while (*s == ' ' || *s == '\t') s++;
        if (*s == '#' || *s == '\n') continue;
        if (sscanf(s, "%63[^=]=%63s", key, val) != 2) continue;
        if (!strcmp(key, "preset")) { preset(val); continue; }
        int v = atoi(val);
        if (v <= 0 && strcmp(key, "predict")) continue;
        if (!strcmp(key, "acquire_r")) C.acquire_r = v;
        else if (!strcmp(key, "track_r")) C.track_r = v;
        else if (!strcmp(key, "fov_limit")) C.fov_limit = v;
        else if (!strcmp(key, "min_px")) C.min_px = v;
        else if (!strcmp(key, "max_px")) C.max_px = v;
        else if (!strcmp(key, "lock_frames")) C.lock_frames = v;
        else if (!strcmp(key, "lost_ms")) C.lost_ms = v;
        else if (!strcmp(key, "stride")) C.stride = v < 1 ? 1 : v;
        else if (!strcmp(key, "smooth")) C.smooth = v;
        else if (!strcmp(key, "gain")) C.gain = v;
        else if (!strcmp(key, "predict")) C.predict = v;
        else if (!strcmp(key, "deadzone")) C.deadzone = v;
        else if (!strcmp(key, "max_step")) C.max_step = v;
        else if (!strcmp(key, "hz")) C.hz = v;
        else if (!strcmp(key, "rmin")) C.rmin = v;
        else if (!strcmp(key, "gmax")) C.gmax = v;
        else if (!strcmp(key, "bmax")) C.bmax = v;
        else if (!strcmp(key, "rg")) C.rg = v;
        else if (!strcmp(key, "rb")) C.rb = v;
    }
    fclose(f);
}

static void screensize(void) {
    FILE *f = popen("wm size", "r");
    if (f) {
        char b[128];
        if (fgets(b, sizeof b, f)) {
            char *x = strchr(b, 'x'); char *c = strchr(b, ':');
            if (x) { SW = atoi(c ? c + 1 : b); SH = atoi(x + 1); }
        }
        pclose(f);
    }
    if (SW < 300 || SH < 300) { SW = 1080; SH = 2400; }
}

static int grab(int *w, int *h) {
    int p[2];
    if (pipe(p)) return -1;
    pid_t pid = fork();
    if (pid == 0) {
        dup2(p[1], 1); close(p[0]); close(p[1]);
        execl("/system/bin/screencap", "screencap", (char *)0);
        _exit(127);
    }
    close(p[1]);
    unsigned char hd[16];
    ssize_t n = read(p[0], hd, 16);
    if (n < 12) { close(p[0]); waitpid(pid, 0, 0); return -1; }
    unsigned int uw, uh;
    memcpy(&uw, hd, 4); memcpy(&uh, hd + 4, 4);
    if (uw < 200 || uh < 200 || uw > 8000 || uh > 8000) { close(p[0]); waitpid(pid, 0, 0); return -1; }
    size_t need = (size_t)uw * uh * 4;
    if (need > fbcap) { free(fb); fb = malloc(need); fbcap = need; }
    if (!fb) { close(p[0]); waitpid(pid, 0, 0); return -1; }
    size_t got = 0;
    while (got < need) {
        ssize_t r = read(p[0], fb + got, need - got);
        if (r <= 0) break;
        got += r;
    }
    close(p[0]); waitpid(pid, 0, 0);
    *w = (int)uw; *h = (int)uh;
    return got == need ? 0 : -1;
}

static inline int tgt(const unsigned char *p) {
    int r = p[0], g = p[1], b = p[2];
    if (r < C.rmin) return 0;
    if (g > C.gmax || b > C.bmax) return 0;
    if (r - g < C.rg || r - b < C.rb) return 0;
    return 1;
}

static int find(int w, int h, int cx, int cy, int rad, int *ox, int *oy, int *omass) {
    int x0 = cx - rad < 0 ? 0 : cx - rad;
    int x1 = cx + rad >= w ? w - 1 : cx + rad;
    int y0 = cy - rad < 0 ? 0 : cy - rad;
    int y1 = cy + rad >= h ? h - 1 : cy + rad;
    int gw = (x1 - x0) / CELL + 1, gh = (y1 - y0) / CELL + 1;
    if (gw * gh > MAXCELLS) return 0;
    int nc = gw * gh;
    memset(cnt, 0, sizeof(int) * nc);
    memset(vis, 0, nc);

    for (int y = y0; y <= y1; y += C.stride) {
        const unsigned char *row = fb + ((size_t)y * w + x0) * 4;
        for (int x = x0; x <= x1; x += C.stride, row += 4 * C.stride)
            if (tgt(row)) {
                int gx = (x - x0) / CELL, gy = (y - y0) / CELL;
                if (gx < gw && gy < gh) cnt[gy * gw + gx]++;
            }
    }

    int minc = C.min_px / 8; if (minc < 2) minc = 2;
    long best = -1; int bx = 0, by = 0, bm = 0;

    for (int i = 0; i < nc; i++) {
        if (vis[i] || cnt[i] < minc) continue;
        int sp = 0; stack_[sp++] = i; vis[i] = 1;
        long mass = 0, sx = 0, sy = 0;
        int mx0 = 1 << 30, mx1 = -1, my0 = 1 << 30, my1 = -1;
        while (sp) {
            int ci = stack_[--sp];
            int gx = ci % gw, gy = ci / gw;
            mass += cnt[ci];
            sx += (long)cnt[ci] * (x0 + gx * CELL + CELL / 2);
            sy += (long)cnt[ci] * (y0 + gy * CELL + CELL / 2);
            if (gx < mx0) mx0 = gx;
            if (gx > mx1) mx1 = gx;
            if (gy < my0) my0 = gy;
            if (gy > my1) my1 = gy;
            for (int dy = -1; dy <= 1; dy++)
                for (int dx = -1; dx <= 1; dx++) {
                    int nx = gx + dx, ny = gy + dy;
                    if (nx < 0 || ny < 0 || nx >= gw || ny >= gh) continue;
                    int ni = ny * gw + nx;
                    if (vis[ni] || cnt[ni] < minc) continue;
                    vis[ni] = 1; stack_[sp++] = ni;
                }
        }
        if (mass < C.min_px || mass > C.max_px) continue;
        int bw = mx1 - mx0 + 1, bh = my1 - my0 + 1;
        if (bw * 3 < bh || bh * 3 < bw) continue;
        int px = (int)(sx / mass), py = (int)(sy / mass);
        long d2 = (long)(px - cx) * (px - cx) + (long)(py - cy) * (py - cy);
        long score = mass * 4000 / (400 + d2 / 3);
        if (score > best) { best = score; bx = px; by = py; bm = (int)mass; }
    }
    if (best < 0) return 0;
    *ox = bx; *oy = by; *omass = bm;
    return 1;
}

static void emit(int t, int c, int v) {
    struct input_event e;
    memset(&e, 0, sizeof e);
    e.type = t; e.code = c; e.value = v;
    write(vfd, &e, sizeof e);
}

static void swipe(int x0, int y0, int x1, int y1) {
    if (x1 < 0) x1 = 0;
    if (x1 >= SW) x1 = SW - 1;
    if (y1 < 0) y1 = 0;
    if (y1 >= SH) y1 = SH - 1;
    emit(EV_ABS, ABS_MT_SLOT, 0);
    emit(EV_ABS, ABS_MT_TRACKING_ID, ++tid);
    emit(EV_ABS, ABS_MT_POSITION_X, x0);
    emit(EV_ABS, ABS_MT_POSITION_Y, y0);
    emit(EV_KEY, BTN_TOUCH, 1);
    emit(EV_SYN, SYN_REPORT, 0);
    usleep(6000);
    emit(EV_ABS, ABS_MT_POSITION_X, x1);
    emit(EV_ABS, ABS_MT_POSITION_Y, y1);
    emit(EV_SYN, SYN_REPORT, 0);
    usleep(6000);
    emit(EV_KEY, BTN_TOUCH, 0);
    emit(EV_ABS, ABS_MT_TRACKING_ID, -1);
    emit(EV_SYN, SYN_REPORT, 0);
}

static int mkvtouch(int w, int h) {
    int fd = open("/dev/uinput", O_WRONLY | O_NONBLOCK);
    if (fd < 0) return -1;
    ioctl(fd, UI_SET_EVBIT, EV_ABS);
    ioctl(fd, UI_SET_EVBIT, EV_KEY);
    ioctl(fd, UI_SET_EVBIT, EV_SYN);
    ioctl(fd, UI_SET_ABSBIT, ABS_MT_SLOT);
    ioctl(fd, UI_SET_ABSBIT, ABS_MT_TRACKING_ID);
    ioctl(fd, UI_SET_ABSBIT, ABS_MT_POSITION_X);
    ioctl(fd, UI_SET_ABSBIT, ABS_MT_POSITION_Y);
    ioctl(fd, UI_SET_ABSBIT, ABS_MT_TOUCH_MAJOR);
    ioctl(fd, UI_SET_KEYBIT, BTN_TOUCH);
    ioctl(fd, UI_SET_PROPBIT, INPUT_PROP_DIRECT);
    struct uinput_user_dev u;
    memset(&u, 0, sizeof u);
    snprintf(u.name, UINPUT_MAX_NAME_SIZE, "bsaim_vtouch");
    u.id.bustype = BUS_VIRTUAL;
    u.id.vendor = 0x1209; u.id.product = 2; u.id.version = 2;
    u.absmin[ABS_MT_POSITION_X] = 0; u.absmax[ABS_MT_POSITION_X] = w - 1;
    u.absmin[ABS_MT_POSITION_Y] = 0; u.absmax[ABS_MT_POSITION_Y] = h - 1;
    u.absmin[ABS_MT_SLOT] = 0; u.absmax[ABS_MT_SLOT] = 1;
    u.absmin[ABS_MT_TOUCH_MAJOR] = 0; u.absmax[ABS_MT_TOUCH_MAJOR] = 255;
    u.absmin[ABS_MT_TRACKING_ID] = 0; u.absmax[ABS_MT_TRACKING_ID] = 65535;
    if (write(fd, &u, sizeof u) < 0 || ioctl(fd, UI_DEV_CREATE) < 0) { close(fd); return -1; }
    return fd;
}

static int keys(void) {
    DIR *d = opendir("/dev/input");
    if (!d) return -1;
    struct dirent *e;
    static unsigned long k[(KEY_MAX / 8) + 1];
    while ((e = readdir(d))) {
        if (strncmp(e->d_name, "event", 5)) continue;
        char p[64];
        snprintf(p, sizeof p, "/dev/input/%s", e->d_name);
        int fd = open(p, O_RDONLY | O_NONBLOCK);
        if (fd < 0) continue;
        memset(k, 0, sizeof k);
        if (ioctl(fd, EVIOCGBIT(EV_KEY, sizeof k), k) >= 0 &&
            (k[KEY_VOLUMEDOWN / 8] & (1 << (KEY_VOLUMEDOWN % 8))) &&
            (k[KEY_VOLUMEUP / 8] & (1 << (KEY_VOLUMEUP % 8)))) { closedir(d); return fd; }
        close(fd);
    }
    closedir(d);
    return -1;
}

static int alive(void) {
    FILE *f = popen("pidof " PKG, "r");
    if (!f) return 0;
    char b[16];
    int r = fgets(b, sizeof b, f) != NULL;
    pclose(f);
    return r;
}

static void calibrar(int w, int h) {
    int cx = w / 2, cy = h / 2, rad = 300;
    static long acc[4096];
    memset(acc, 0, sizeof acc);
    for (int y = cy - rad; y < cy + rad; y += 2)
        for (int x = cx - rad; x < cx + rad; x += 2) {
            const unsigned char *p = fb + ((size_t)y * w + x) * 4;
            if (p[0] < 90) continue;
            int key = ((p[0] >> 4) << 8) | ((p[1] >> 4) << 4) | (p[2] >> 4);
            acc[key]++;
        }
    lg("CAL top colores:\n");
    for (int n = 0; n < 8; n++) {
        long best = 0; int bk = -1;
        for (int i = 0; i < 4096; i++) if (acc[i] > best) { best = acc[i]; bk = i; }
        if (bk < 0 || best < 20) break;
        lg("  r=%d g=%d b=%d n=%ld\n", ((bk >> 8) & 15) * 16 + 8, ((bk >> 4) & 15) * 16 + 8, (bk & 15) * 16 + 8, best);
        acc[bk] = 0;
    }
}

int main(int argc, char **argv) {
    const char *cp = "/data/adb/bloodstrike_aim/bsaim.conf", *lp = NULL;
    int cal = 0;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-c") && i + 1 < argc) cp = argv[++i];
        else if (!strcmp(argv[i], "-l") && i + 1 < argc) lp = argv[++i];
        else if (!strcmp(argv[i], "-cal")) cal = 1;
    }
    if (lp) LOGFD = open(lp, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    cfg(cp);
    signal(SIGTERM, onsig);
    signal(SIGINT, onsig);
    screensize();

    if (cal) {
        int w, h;
        if (grab(&w, &h) == 0) calibrar(w, h);
        return 0;
    }

    vfd = mkvtouch(SW, SH);
    if (vfd < 0) { lg("ERROR uinput\n"); return 1; }
    kfd = keys();
    lg("v2 %dx%d acq=%d smooth=%d\n", SW, SH, C.acquire_r, C.smooth);

    int cx = SW / 2, cy = SH / 2;
    int tick = 1000000 / (C.hz > 0 ? C.hz : 18);
    int locked = 0, confirm = 0, lost = 0, tickn = 0, live = 0;
    double vx = 0, vy = 0;

    while (run) {
        if (kfd >= 0) {
            struct input_event ev;
            while (read(kfd, &ev, sizeof ev) == sizeof ev) {
                if (ev.type != EV_KEY || ev.value != 1) continue;
                if (ev.code == KEY_VOLUMEDOWN) { enabled = !enabled; lg("on=%d\n", enabled); }
                if (ev.code == KEY_VOLUMEUP) {
                    int w, h;
                    if (grab(&w, &h) == 0) calibrar(w, h);
                }
            }
        }
        if (++tickn % 30 == 0) live = alive();
        if (!enabled || !live) { usleep(120000); continue; }

        int w, h;
        if (grab(&w, &h) != 0) { usleep(tick); continue; }

        int px = cx + (int)(vx * C.predict / 100.0);
        int py = cy + (int)(vy * C.predict / 100.0);
        int rad = locked ? C.track_r : C.acquire_r;
        int tx, ty, mass;

        if (find(w, h, px, py, rad, &tx, &ty, &mass)) {
            int ddx = tx - cx, ddy = ty - cy;
            int adx = ddx < 0 ? -ddx : ddx, ady = ddy < 0 ? -ddy : ddy;
            if (!locked) {
                if (++confirm >= C.lock_frames) { locked = 1; lost = 0; lg("LOCK m=%d\n", mass); }
            } else if (adx + ady > C.fov_limit) {
                locked = 0; confirm = 0; vx = vy = 0;
            }
            if (locked) {
                lost = 0;
                vx = vx * 0.55 + (double)ddx * 0.45;
                vy = vy * 0.55 + (double)ddy * 0.45;
                if ((adx > ady ? adx : ady) > C.deadzone) {
                    int fx = (int)(ddx * C.smooth * C.gain / 10000.0);
                    int fy = (int)(ddy * C.smooth * C.gain / 10000.0);
                    if (fx > C.max_step) fx = C.max_step;
                    if (fx < -C.max_step) fx = -C.max_step;
                    if (fy > C.max_step) fy = C.max_step;
                    if (fy < -C.max_step) fy = -C.max_step;
                    swipe(cx, cy, cx + fx, cy + fy);
                }
            } else {
                confirm = 0;
            }
        } else {
            confirm = 0;
            if (locked && (lost += tick / 1000) > C.lost_ms) { locked = 0; vx = vy = 0; }
        }
        usleep(tick);
    }
    if (vfd >= 0) { ioctl(vfd, UI_DEV_DESTROY); close(vfd); }
    return 0;
}
