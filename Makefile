CC      ?= cc
CFLAGS  ?= -O2

verificateur.exe: verificateur.c
	$(CC) $(CFLAGS) -o $@ $<

.PHONY: verify verify-petit verify-1e6 verify-py clean

# verification C complete sur le run principal
verify: verificateur.exe
	./verificateur.exe 1000000 run_1e6

# smoke test rapide (petit run)
verify-petit: verificateur.exe
	./verificateur.exe 100000 run_petit

verify-1e6: verify

# verification Python/numpy (petit run)
verify-py:
	python verificateur.py 100000 run_petit

# suite anti-corruption : les 4 DOIVENT echouer (exit != 0)
verify-corrupt: verificateur.exe
	@for d in run_corrupt_rtable run_corrupt_skip \
	          run_corrupt_goulot run_corrupt_trunc ; do \
	  echo "=== $$d ===" ; \
	  if ./verificateur.exe 100000 $$d ; then \
	    echo "!!! $$d ACCEPTE - ECHEC TEST" ; exit 1 ; \
	  else echo "$$d rejete (attendu)" ; fi ; \
	done

clean:
	rm -f verificateur.exe
