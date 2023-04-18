############################################################################
# Copyright 2021-2022 Catherine Dubois, Nicolas Magaud and Alain Giorgetti #
# Samovar - ICube - FEMTO-ST institute                                     #
############################################################################

############################################################################
#      This file is distributed under the terms of the                     #
#      GNU General Public License Version 3                                #
############################################################################

FILES=_CoqProject Makefile __EXCLUDED_OUTPUT_PATTERNS \
 prelude.v \
 familyInterface.v \
 closable.v        \
 ucs.v             \
 open.v            \
 BT17.v            \
 automation.v      \
 label.v           \
 qc_closable.v val_qc_closable.v qc_ucs.v val_qc_ucs.v qc_open.v val_qc_open.v # generators and tests

.PHONY: all clean

all:
	coq_makefile -f _CoqProject -o CoqMakefile
	make -f CoqMakefile clean
	make -f CoqMakefile 2> /dev/null | grep -v --file=__EXCLUDED_OUTPUT_PATTERNS

clean:
	rm -f *.glob *.vo .*.aux *.bak *.cmi *.cmx *.o *.vok *.vos

