# -- [ Makefile ]
#
# Makefile for the project.
#
# Copyright : (c) Jan de Muijnck-Hughes
# License   : see LICENSE
#
# -- [ EOH ]

PROJECT=systemw
IDRIS2=idris2
HYPERFINE=hyperfine

TARGETDIR = ${CURDIR}/build/exec
TARGET = ${TARGETDIR}/${PROJECT}

# [ Core Project Definition ]

.PHONY: systemw systemw-test-build systemw-test-run systemw-test-run-re systemw-test-update systemw-bench

systemw:
	$(IDRIS2) --build ${PROJECT}.ipkg

systemw-test-build:
	${MAKE} -C tests testbin IDRIS2=$(IDRIS2)

systemw-test-run: systemw-test-build
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 UPDATE='' \
			 ONLY=$(ONLY)

systemw-test-run-re: systemw-test-build
	${MAKE} -C tests test-re \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 ONLY=$(ONLY)

systemw-test-update: systemw-test-build
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 ONLY=$(ONLY)

systemw-bench: systemw systemw-test-build
	${ECHO} "Todo"

#	$(HYPERFINE) --warmup 10 '${MAKE} -C tests test SYSTEMV_BIN=$(TARGET) SYSTEMV_TEST_U=$(SYSTEMV_TEST_U) SYSTEMV_TEST_O=$(SYSTEMV_TEST_O)'


# [ Housekeeping ]

.PHONY: clobber clean

clean:
	$(IDRIS2) --clean ${PROJECT}.ipkg
	${MAKE} -C tests clean

clobber: clean
	$(IDRIS2) --clean ${PROJECT}.ipkg
	${MAKE} -C tests clobber
	${RM} -rf build/

# -- [ EOF ]
