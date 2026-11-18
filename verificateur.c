/* verificateur.c -- verificateur C99 INDEPENDANT des certificats
   CONJ-2COMP (digraphe de re-pairage : table r, puits par niveau,
   goulots, passe tau interieure).
   Ne fait confiance a rien du producteur : r(m) est REENUMERE par
   la liste des premiers (jamais la FFT), les minima de classe, les
   goulots, N(u1,u2), L_k/M_cut et la passe tau sont recalcules.
   Usage : verificateur.exe <N> <dossier_certs>
   Compile : cc -O2 -o verificateur.exe verificateur.c            */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long long u64;
typedef long long i64;

static u8 *P;          /* primalite 0..2N+1 */
static u32 *primes;    /* liste des premiers <= 2N */
static int npr;
static u64 N;
static u32 *rtab;      /* r(m) reenumere, m <= N */
static u32 *T;         /* buffer rayons */

static void die(const char *m) { fprintf(stderr, "FATAL %s\n", m); exit(1); }

static void sieve(void) {
    u64 i, k, lim = 2 * N + 1;
    P = malloc(lim + 1); if (!P) die("alloc P");
    memset(P, 1, lim + 1); P[0] = P[1] = 0;
    for (i = 2; i * i <= lim; i++)
        if (P[i]) for (k = i * i; k <= lim; k += i) P[k] = 0;
    npr = 0;
    for (i = 2; i <= lim; i++) npr += P[i];
    primes = malloc((npr + 1) * sizeof(u32)); if (!primes) die("alloc primes");
    npr = 0;
    for (i = 2; i <= lim; i++) if (P[i]) primes[npr++] = (u32)i;
}

/* borne sup stricte : indice du 1er premier > x */
static int pgt(u64 x) {
    int lo = 0, hi = npr;
    while (lo < hi) { int md = (lo + hi) >> 1; if (primes[md] <= x) lo = md + 1; else hi = md; }
    return lo;
}
static int pge(u64 x) {
    int lo = 0, hi = npr;
    while (lo < hi) { int md = (lo + hi) >> 1; if (primes[md] < x) lo = md + 1; else hi = md; }
    return lo;
}

/* S(m) dans T (trie croissant) : t = p - m pour p premier in (m,2m),
   garde ssi P[2m-p]. Retourne le nombre. */
static int rays(u64 m) {
    int lo = pgt(m), hi = pge(2 * m), c = 0, i;
    for (i = lo; i < hi; i++) {
        u32 p = primes[i];
        if (P[2 * m - p]) T[c++] = p - (u32)m;
    }
    return c;
}

static int nchild_valid(u64 m, int rr, u64 kthr) {
    /* >=1 si une paire de rayons donne un enfant n<m avec r(n)>=kthr */
    int i, d;
    for (d = 1; d < rr; d++)
        for (i = 0; i + d < rr; i++) {
            u64 a = T[i], b = T[i + d];
            u64 n1 = m - (b - a) / 2, n2 = m - (a + b) / 2;
            if ((n1 >= 4 && n1 < m && rtab[n1] >= kthr)
                || (n2 >= 4 && n2 < m && rtab[n2] >= kthr))
                return 1;
        }
    return 0;
}

static i64 bridge_max(u64 m) {
    if (!P[2 * m - 3]) return -1;
    int rr = rays(m), i;
    i64 bm = 0;
    for (i = 0; i < rr; i++) {
        u64 a = T[i];
        if (a == m - 3) continue;
        u64 n1 = m - (m - 3 - a) / 2, n2 = m - (a + m - 3) / 2;
        if (n1 >= 4 && n1 < m && (i64)rtab[n1] > bm) bm = rtab[n1];
        if (n2 >= 4 && n2 < m && (i64)rtab[n2] > bm) bm = rtab[n2];
    }
    return bm;
}

static i64 full_max(u64 m) {
    int rr = rays(m), i, d;
    i64 M = 0;
    for (d = 1; d < rr; d++)
        for (i = 0; i + d < rr; i++) {
            u64 a = T[i], b = T[i + d];
            u64 n1 = m - (b - a) / 2, n2 = m - (a + b) / 2;
            if (n1 >= 4 && n1 < m && (i64)rtab[n1] > M) M = rtab[n1];
            if (n2 >= 4 && n2 < m && (i64)rtab[n2] > M) M = rtab[n2];
        }
    return M;
}

/* petit cache m -> i64 (bridge_max / full_max par m distinct) */
#define CCH 65536
static u64 ckey[2][CCH]; static i64 cval[2][CCH]; static u8 chas[2][CCH];
static i64 cached(int which, u64 m) {
    u64 h = (m * 0x9E3779B97F4A7C15ULL) & (CCH - 1);
    if (chas[which][h] && ckey[which][h] == m) return cval[which][h];
    i64 v = which ? full_max(m) : bridge_max(m);
    chas[which][h] = 1;
    ckey[which][h] = m; cval[which][h] = v;
    return v;
}

static u8 *fdata; static size_t flen;
static void load(const char *dir, const char *fn) {
    char path[1024];
    snprintf(path, sizeof path, "%s/%s", dir, fn);
    FILE *f = fopen(path, "rb"); if (!f) die(path);
    fseek(f, 0, SEEK_END); flen = (size_t)ftell(f); fseek(f, 0, SEEK_SET);
    fdata = malloc(flen ? flen : 1); if (!fdata) die("alloc fdata");
    if (flen && fread(fdata, 1, flen, f) != flen) die("read");
    fclose(f);
}
static u32 rd32(const u8 *p) { u32 v; memcpy(&v, p, 4); return v; }
static u64 rd64(const u8 *p) { u64 v; memcpy(&v, p, 8); return v; }
static u16 rd16(const u8 *p) { u16 v; memcpy(&v, p, 2); return v; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s N dir\n", argv[0]); return 1; }
    N = strtoull(argv[1], 0, 10);
    clock_t t0 = clock();
    sieve();
    fprintf(stderr, "crible 2N+2 en %.1fs (pi=%d)\n",
            (double)(clock() - t0) / CLOCKS_PER_SEC, npr);
    /* ancres du crible (re-comptees par le verificateur) */
    {
        u64 target_pi = (N == 1000000) ? 148933 : (N == 100000) ? 17984 : 0;
        if (target_pi && (u64)npr != target_pi) {
            printf("!!! ANCRE CIBLE INVALIDE : pi(2N)=%d attendu %llu\n",
                   npr, target_pi);
            return 3;
        }
    }
    T = malloc((npr + 2) * sizeof(u32)); if (!T) die("alloc T");

    /* ---------- r(m) reenumere : #{p premier in (m,2m) : 2m-p premier} -- */
    rtab = calloc(N + 1, sizeof(u32)); if (!rtab) die("alloc rtab");
    {
        u64 m; int i;
        for (m = 4; m <= N; m++) {
            int lo = pgt(m), hi = pge(2 * m); u32 c = 0;
            for (i = lo; i < hi; i++) c += P[2 * m - primes[i]];
            rtab[m] = c;
        }
    }
    fprintf(stderr, "rtable reenumeree en %.1fs\n",
            (double)(clock() - t0) / CLOCKS_PER_SEC);

    /* ---------- 1. certs_rtable.bin ---------- */
    load(argv[2], "certs_rtable.bin");
    {
        int nbad = 0; u64 m;
        if (flen < 24 || memcmp(fdata, "RT2C", 4) || rd32(fdata + 4) != 1)
            { printf("!!! CERTIFICAT INVALIDE rtable : en-tete\n"); return 3; }
        if (rd64(fdata + 8) != N) { printf("!!! N incoherent\n"); return 3; }
        u64 cnt = rd64(fdata + 16);
        if (cnt != N + 1 || flen != 24 + 2 * (N + 1)) {
            printf("!!! CERTIFICAT INVALIDE rtable : taille %zu o != %llu o\n",
                   flen, 24 + 2 * (N + 1));
            return 3;
        }
        for (m = 0; m <= N; m++) {
            u16 v = rd16(fdata + 24 + 2 * m);
            if (v != rtab[m]) {
                if (nbad < 10)
                    printf("  r mismatch m=%llu cert=%u recalc=%u\n", m, v, rtab[m]);
                nbad++;
            }
        }
        printf("RTABLE : %llu valeurs comparees ; mismatches=%d\n", N + 1, nbad);
        if (nbad) { printf("!!! TABLE R INVALIDE\n"); return 3; }
        free(fdata);
    }

    /* ---------- minima de classe mu_c(k) ---------- */
    {
        u64 m; int KALL = 0;
        for (m = 4; m <= N; m++) if ((int)rtab[m] > KALL) KALL = rtab[m];
        u64 *mu[3]; i64 maxR[3] = {0, 0, 0}; int c;
        for (c = 0; c < 3; c++) {
            mu[c] = calloc(KALL + 1, sizeof(u64));
            if (!mu[c]) die("alloc mu");
        }
        for (m = 4; m <= N; m++) {
            c = m % 3;
            if ((i64)rtab[m] > maxR[c]) {
                i64 k;
                for (k = maxR[c] + 1; k <= (i64)rtab[m]; k++) mu[c][k] = m;
                maxR[c] = rtab[m];
            }
        }
        int Kvalid = (int)(maxR[0] < maxR[1] ? maxR[0] : maxR[1]);
        if (maxR[2] < Kvalid) Kvalid = (int)maxR[2];

        /* ---------- 2. certs_puits.bin ---------- */
        load(argv[2], "certs_puits.bin");
        {
            int nbad = 0, npuits_tot = 0;
            u64 kf, count;
            if (flen < 32 || memcmp(fdata, "PU2C", 4) || rd32(fdata + 4) != 1)
                { printf("!!! CERTIFICAT INVALIDE puits : en-tete\n"); return 3; }
            if (rd64(fdata + 8) != N) { printf("!!! N incoherent\n"); return 3; }
            kf = rd64(fdata + 16); count = rd64(fdata + 24);
            if ((i64)kf != Kvalid) {
                printf("!!! Kvalid cert=%llu recalc=%d\n", kf, Kvalid);
                return 3;
            }
            if (count != (u64)(Kvalid - 1) || flen != 32 + 20 * count) {
                printf("!!! CERTIFICAT INVALIDE puits : taille/compte\n");
                return 3;
            }
            int k;
            u8 *masks = calloc(Kvalid + 1, 1); if (!masks) die("alloc masks");
            for (k = 2; k <= Kvalid; k++) {
                const u8 *rec = fdata + 32 + 20 * (size_t)(k - 2);
                u32 rk = rd32(rec), mu0 = rd32(rec + 4), mu1 = rd32(rec + 8),
                    mu2 = rd32(rec + 12);
                u8 mask = rec[16], cnt = rec[17];
                if ((int)rk != k || mu0 != mu[0][k] || mu1 != mu[1][k]
                    || mu2 != mu[2][k]) {
                    printf("  puits k=%d : minima cert=(%u,%u,%u) recalc=(%llu,%llu,%llu)\n",
                           k, mu0, mu1, mu2, mu[0][k], mu[1][k], mu[2][k]);
                    nbad++; continue;
                }
                int own = 0;
                if (mu0 == (mu0 < mu1 ? (mu0 < mu2 ? mu0 : mu2)
                                      : (mu1 < mu2 ? mu1 : mu2))
                    || cached(1, mu0) < k) own |= 1;
                if (cached(0, mu1) < k) own |= 2;
                if (cached(0, mu2) < k) own |= 4;
                if (own != mask || cnt != (own & 1) + ((own >> 1) & 1)
                                        + ((own >> 2) & 1)) {
                    printf("  puits k=%d : mask cert=%u recalc=%d\n",
                           k, mask, own);
                    nbad++; continue;
                }
                masks[k] = mask;
                npuits_tot += cnt;
            }
            printf("PUITS : %d niveaux verifies ; total puits=%d ; mismatches=%d\n",
                   Kvalid - 1, npuits_tot, nbad);
            if (nbad) { printf("!!! PUITS INVALIDES\n"); return 3; }
            free(fdata);

            /* ---------- puits niveau 1 ---------- */
            load(argv[2], "puits_k1.txt");
            {
                int i = 0, n1 = 0; u64 w[64];
                char *buf = malloc(flen + 1);
                memcpy(buf, fdata, flen); buf[flen] = 0;
                char *s = strtok(buf, "\n");
                while (s) { if (i < 64) w[i++] = strtoull(s, 0, 10);
                            s = strtok(0, "\n"); }
                int nbad1 = 0;
                for (m = 4; m <= N; m++) if (rtab[m] == 1) {
                    if (n1 < i && w[n1] == m) n1++;
                    else { printf("  k1 : puits recalc m=%llu absent du fichier\n", m);
                           nbad1++; }
                }
                printf("PUITS_K1 : %d puits recalcules, %d lus ; mismatches=%d\n",
                       n1, i, nbad1 + (i - n1 > 0 ? i - n1 : 0));
                if (nbad1 || i != n1) { printf("!!! PUITS_K1 INVALIDE\n"); return 3; }
                free(fdata); free(buf);
            }

            /* ---------- 3. ak_bfile.txt ---------- */
            load(argv[2], "ak_bfile.txt");
            {
                char *buf = malloc(flen + 1);
                memcpy(buf, fdata, flen); buf[flen] = 0;
                int nbad = 0, lines = 0;
                u64 n1 = 0, m3;
                for (m3 = 4; m3 <= N; m3++) n1 += (rtab[m3] == 1);
                char *s = strtok(buf, "\n");
                while (s) {
                    u64 kk, vv; lines++;
                    if (sscanf(s, "%llu %llu", &kk, &vv) != 2 || (int)kk != lines) {
                        printf("  ak bfile ligne %d illisible '%s'\n", lines, s);
                        nbad++; break;
                    }
                    if ((int)kk == 1) {
                        if (vv != n1) { printf("  a(1) cert=%llu recalc=%llu\n", vv, n1); nbad++; }
                    } else if ((int)kk <= Kvalid) {
                        int own = (masks[kk] & 1) + ((masks[kk] >> 1) & 1)
                                + ((masks[kk] >> 2) & 1);
                        if ((int)vv != own) {
                            printf("  a(%llu) cert=%llu recalc=%d\n", kk, vv, own);
                            nbad++;
                        }
                    } else { printf("  ak bfile : k=%llu > Kvalid\n", kk); nbad++; }
                    s = strtok(0, "\n");
                }
                if (lines != Kvalid) {
                    printf("  ak bfile : %d lignes != Kvalid %d\n", lines, Kvalid);
                    nbad++;
                }
                printf("AK_BFILE : %d lignes, %d mismatches\n", lines, nbad);
                if (nbad) { printf("!!! AK_BFILE INVALIDE\n"); return 3; }
                free(fdata); free(buf);
            }
            free(masks);
        }
        /* garder mu/maxR pour goulots ci-dessous */
        {
            /* ---------- passe tau interieure ---------- */
            u64 m2; int c2, k;
            u64 *G = calloc(KALL + 2, sizeof(u64)); if (!G) die("alloc G");
            for (m2 = 4; m2 <= N; m2++)
                if (m2 > G[rtab[m2]]) G[rtab[m2]] = m2;
            u64 run = 0;
            u64 *Lka = calloc(Kvalid + 1, sizeof(u64));
            u64 *Mca = calloc(Kvalid + 1, sizeof(u64));
            for (k = 1; k <= Kvalid; k++) {
                if (G[k - 1] > run) run = G[k - 1];
                Lka[k] = run;
            }
            int KCUT = 1; u64 Bmax = 0;
            for (k = 2; k <= Kvalid; k++) {
                u64 L = Lka[k];
                Mca[k] = (L >= 4) ? L + 1 + (L - 4) / (2 * (u64)k - 3) : L + 1;
                if (Mca[k] <= N) { KCUT = k; if (Mca[k] > Bmax) Bmax = Mca[k]; }
            }
            Bmax += 2;
            i64 Rprev[3] = {0, 0, 0};
            u64 testes = 0, parasites = 0;
            for (m2 = 6; m2 <= Bmax; m2++) {
                c2 = m2 % 3;
                i64 tau = rtab[m2] < (u64)Rprev[c2] ? rtab[m2] : Rprev[c2];
                if (tau >= 2) {
                    int rr = rays(m2);
                    testes++;
                    if (rr < 2 || !nchild_valid(m2, rr, (u64)tau)) {
                        parasites++;
                        if (parasites <= 10)
                            printf("  PARASITE m=%llu classe=%d r=%u tau=%lld\n",
                                   m2, c2, rtab[m2], tau);
                    }
                }
                if ((i64)rtab[m2] > Rprev[c2]) Rprev[c2] = rtab[m2];
            }
            printf("TAU : KCUT=%d B_max=%llu vitaux_testes=%llu parasites=%llu\n",
                   KCUT, Bmax, testes, parasites);
            if (parasites) {
                printf("!!! PUITS INTERIEUR DETECTE - CONTRE-EXEMPLE\n");
                return 2;
            }
            /* ---------- passe 2 : vitaux tau >= 7227 sur [6,N] ---------- */
            {
                i64 Rprev2[3] = {0, 0, 0};
                u64 testes2 = 0, parasites2 = 0;
                for (m2 = 6; m2 <= N; m2++) {
                    c2 = m2 % 3;
                    i64 tau2 = rtab[m2] < (u64)Rprev2[c2] ? rtab[m2] : Rprev2[c2];
                    if (tau2 >= 7227) {
                        int rr = rays(m2);
                        testes2++;
                        if (rr < 2 || !nchild_valid(m2, rr, (u64)tau2)) {
                            parasites2++;
                            if (parasites2 <= 10)
                                printf("  PARASITE_HI m=%llu classe=%d r=%u tau=%lld\n",
                                       m2, c2, rtab[m2], tau2);
                        }
                    }
                    if ((i64)rtab[m2] > Rprev2[c2]) Rprev2[c2] = rtab[m2];
                }
                printf("TAU_HI : seuil=7227 vitaux_testes=%llu parasites=%llu\n",
                       testes2, parasites2);
                if (parasites2) {
                    printf("!!! PUITS INTERIEUR HAUT DETECTE - CONTRE-EXEMPLE\n");
                    return 2;
                }
            }
            free(G); free(Lka); free(Mca);
        }

        /* ---------- 4. certs_goulots.bin ---------- */
        load(argv[2], "certs_goulots.bin");
        {
            if (flen < 24 || memcmp(fdata, "GO2C", 4) || rd32(fdata + 4) != 1)
                { printf("!!! CERTIFICAT INVALIDE goulots : en-tete\n"); return 3; }
            if (rd64(fdata + 8) != N) { printf("!!! N incoherent\n"); return 3; }
            u64 count = rd64(fdata + 16);
            if (flen != 24 + 24 * count) {
                printf("!!! CERTIFICAT INVALIDE goulots : taille\n"); return 3;
            }
            /* re-extraction verbatim */
            i64 R1[3] = {0, 0, 0}, R2[3] = {0, 0, 0}; u64 M1[3] = {0, 0, 0};
            u64 m2, gi = 0; int nbad = 0, pm = 0, minN = -1;
            for (m2 = 6; m2 <= N; m2++) {
                int c2 = m2 % 3;
                i64 thr = (i64)rtab[m2] < R1[c2] ? (i64)rtab[m2] : R1[c2];
                if (R2[c2] < thr && R1[c2] > 0) {
                    /* goulot (u1,u2,k,ru2,ru1,c,pont) */
                    u64 u1 = M1[c2], u2 = m2, v = u2 - u1;
                    int pmort = !P[2 * u2 - 3];
                    if (gi >= count) {
                        printf("  goulot recalcule en trop : (%llu,%llu) a m=%llu\n",
                               u1, u2, m2);
                        nbad++;
                    } else {
                        const u8 *rec = fdata + 24 + 24 * (size_t)gi;
                        u32 cu1 = rd32(rec), cu2 = rd32(rec + 4),
                            ck = rd32(rec + 8), cru1 = rd32(rec + 12),
                            cru2 = rd32(rec + 16);
                        u8 cc = rec[20], cpm = rec[21];
                        u16 cN = rd16(rec + 22);
                        /* N recalcule */
                        u64 p, Nw = 0;
                        for (p = 3; p < u1; p++)
                            if (P[p] && P[2 * u1 - p] && P[p + 2 * v]
                                && P[2 * u2 - p]) Nw++;
                        {
                            u64 ex = 2 * u1 - u2;
                            if (ex >= 3 && ex < u1 && P[ex] && P[2 * u1 - ex]
                                && P[ex + 2 * v] && P[2 * u2 - ex]) Nw--;
                        }
                        if (cu1 != u1 || cu2 != u2 || (i64)ck != thr
                            || cru1 != R1[c2] || cru2 != rtab[u2]
                            || cc != c2 || cpm != pmort || cN != Nw) {
                            printf("  goulot #%llu mismatch : cert(%u,%u,k%u,%u,%u,c%u,pm%u,N%u) recalc(%llu,%llu,k%lld,%lld,%u,c%d,pm%d,N%llu)\n",
                                   gi, cu1, cu2, ck, cru1, cru2, cc, cpm, cN,
                                   u1, u2, thr, R1[c2], rtab[u2], c2, pmort, Nw);
                            nbad++;
                        }
                        if (pmort) { pm++;
                            if (minN < 0 || (int)Nw < minN) minN = (int)Nw; }
                        gi++;
                    }
                }
                if ((i64)rtab[m2] > R1[c2]) {
                    R2[c2] = R1[c2]; R1[c2] = rtab[m2]; M1[c2] = m2;
                } else if ((i64)rtab[m2] > R2[c2]) {
                    R2[c2] = rtab[m2];
                }
            }
            if (gi != count) {
                printf("  goulots : recalcules %llu != count cert %llu\n", gi, count);
                nbad++;
            }
            printf("GOULOTS : %llu verifies ; pont-mort=%d ; minN_pm=%d ; mismatches=%d\n",
                   gi, pm, minN, nbad);
            if (nbad) { printf("!!! GOULOTS INVALIDES\n"); return 3; }
            if (minN == 0) {
                printf("!!! N=0 SUR GOULOT PONT-MORT - CONTRE-EXEMPLE GOULOT\n");
                return 2;
            }
            free(fdata);
        }

        /* ---------- 5. m1_bfile.txt ---------- */
        load(argv[2], "m1_bfile.txt");
        {
            char *buf = malloc(flen + 1);
            memcpy(buf, fdata, flen); buf[flen] = 0;
            int nbad = 0, lines = 0;
            char *s = strtok(buf, "\n");
            while (s) {
                u64 kk, vv; lines++;
                if (sscanf(s, "%llu %llu", &kk, &vv) != 2 || (int)kk != lines) {
                    printf("  m1 bfile ligne %d illisible\n", lines); nbad++; break;
                }
                if ((int)kk <= Kvalid) {
                    u64 own = mu[0][kk] < mu[1][kk]
                              ? (mu[0][kk] < mu[2][kk] ? mu[0][kk] : mu[2][kk])
                              : (mu[1][kk] < mu[2][kk] ? mu[1][kk] : mu[2][kk]);
                    if (vv != own) { printf("  m1(%llu) cert=%llu recalc=%llu\n", kk, vv, own); nbad++; }
                } else { printf("  m1 bfile : k=%llu > Kvalid\n", kk); nbad++; }
                s = strtok(0, "\n");
            }
            if (lines != Kvalid) { printf("  m1 bfile : %d lignes != Kvalid\n", lines); nbad++; }
            printf("M1_BFILE : %d mismatches\n", nbad);
            if (nbad) { printf("!!! M1_BFILE INVALIDE\n"); return 3; }
            free(fdata); free(buf);
        }
        for (c = 0; c < 3; c++) free(mu[c]);
    }

    printf("==================================================\n");
    printf("VERDICT C (independant) N=%llu %.1fs\n", N,
           (double)(clock() - t0) / CLOCKS_PER_SEC);
    printf("  chaine : r-table + puits + goulots + tau verifies\n");
    return 0;
}
