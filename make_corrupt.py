# make_corrupt.py -- regenere la suite anti-corruption a partir de run_petit.
# 4 fixtures, chacun DOIT etre rejete par les deux verificateurs :
#   run_corrupt_rtable/  : une valeur r(m) mutee dans certs_rtable.bin
#   run_corrupt_skip/    : un record-niveau supprime de certs_puits.bin
#   run_corrupt_goulot/  : N(u1,u2) mis a 0 sur un goulot pont-mort
#   run_corrupt_trunc/   : certs_puits.bin tronque en plein record
# Usage : python make_corrupt.py [src=run_petit]
import sys, os, struct, shutil

SRC = sys.argv[1] if len(sys.argv) > 1 else "run_petit"
FILES = ["certs_rtable.bin", "certs_puits.bin", "certs_goulots.bin",
         "puits_k1.txt", "ak_bfile.txt", "m1_bfile.txt", "stats.txt",
         "producteur_log.txt"]


def clone(dst, note):
    if os.path.isdir(dst):
        shutil.rmtree(dst)
    os.makedirs(dst)
    for fn in FILES:
        shutil.copy2(os.path.join(SRC, fn), os.path.join(dst, fn))
    with open(os.path.join(dst, "NOTE.txt"), "w", encoding="utf-8") as f:
        f.write(note)


# ---------- 1. rtable mutee ----------
d = os.path.join(SRC, "certs_rtable.bin")
data = bytearray(open(d, "rb").read())
# record m=5000 (offset 24 + 2*5000) : +1 sur la valeur u16
off = 24 + 2 * 5000
v = struct.unpack_from("<H", data, off)[0]
struct.pack_into("<H", data, off, v + 1)
clone("run_corrupt_rtable",
      "mutation : r(5000) incremente de 1 dans certs_rtable.bin\n"
      "(offset %d, %d -> %d)\n" % (off, v, v + 1))
open(os.path.join("run_corrupt_rtable", "certs_rtable.bin"), "wb").write(data)

# ---------- 2. record-niveau supprime ----------
data = open(d := os.path.join(SRC, "certs_puits.bin"), "rb").read()
hdr = bytearray(data[:32])                   # <4sIQQQ> = 32 o
count = struct.unpack_from("<Q", hdr, 24)[0]
struct.pack_into("<Q", hdr, 24, count - 1)   # compte ajuste (niveau saute)
body = data[32:]
# suppression du record du niveau k=10 (index 8)
i = 8
body2 = body[:20 * i] + body[20 * (i + 1):]
clone("run_corrupt_skip",
      "mutation : record du niveau k=10 supprime de certs_puits.bin\n"
      "(count %d -> %d ; le verificateur doit detecter le saut de niveau)\n"
      % (count, count - 1))
open(os.path.join("run_corrupt_skip", "certs_puits.bin"), "wb").write(
    bytes(hdr) + body2)

# ---------- 3. N mutee sur un goulot pont-mort ----------
data = bytearray(open(os.path.join(SRC, "certs_goulots.bin"), "rb").read())
REC = 24
pm_idx = None
for i in range((len(data) - 24) // REC):
    if data[24 + i * REC + 21]:            # champ pont_mort
        pm_idx = i
        break
struct.pack_into("<H", data, 24 + pm_idx * REC + 22, 0)  # N -> 0
clone("run_corrupt_goulot",
      "mutation : N(u1,u2) force a 0 sur le goulot pont-mort #%d\n"
      "(le verificateur recompte N et doit rejeter)\n" % pm_idx)
open(os.path.join("run_corrupt_goulot", "certs_goulots.bin"), "wb").write(data)

# ---------- 4. puits tronque ----------
data = open(os.path.join(SRC, "certs_puits.bin"), "rb").read()
clone("run_corrupt_trunc",
      "mutation : certs_puits.bin coupe a mi-record (7 octets du dernier)\n"
      "(le controle de taille doit rejeter)\n")
open(os.path.join("run_corrupt_trunc", "certs_puits.bin"), "wb").write(
    data[:-7])

print("4 fixtures regenerees depuis %s" % SRC)
