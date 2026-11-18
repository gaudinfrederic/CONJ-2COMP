# make_rtable.py -- regenere rtable_1M.npy depuis le certificat signe.
#
# Usage : python make_rtable.py [run_1e6]
#   lit  <run>/certs_rtable.bin  (format RT2C, cf SPECS_CERTS.md)
#   ecrit rtable_1M.npy        (table r(m), m = 0..N, u16)
#
# Tous les scripts falsif_*.py / test_rechute.py chargent ce .npy ;
# le regenerer depuis le certificat (plutot que re-calculer par FFT)
# garantit que les falsificateurs tournent sur la donnee certifiee.

import sys, os, struct
import numpy as np

def main(run="run_1e6", out="rtable_1M.npy"):
    path = os.path.join(run, "certs_rtable.bin")
    with open(path, "rb") as f:
        blob = f.read()
    magic, ver, N, count = struct.unpack_from("<4sIQQ", blob, 0)
    assert magic == b"RT2C", "magic RT2C attendu"
    assert ver == 1, "version 1 attendue"
    assert count == N + 1
    assert len(blob) == 24 + 2 * count, "taille fichier incoherente"
    r = np.frombuffer(blob, dtype="<u2", count=count, offset=24).copy()
    np.save(out, r)
    print("%s : %d valeurs, max r=%d -> %s" % (path, count, int(r.max()), out))

if __name__ == "__main__":
    main(*sys.argv[1:])
