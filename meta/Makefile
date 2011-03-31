############################################################################
#
#  Primary targets:
#    all           - the default target; synonym for 'coq'
#    coq           - builds all .vo files
#    doc           - synonym for 'documentation'
#    documentation - builds all html documentation
#    clean         - removes generated files
#
#  Other targets (intended to be used by the developers of this library):
#    gens          - builds generated .v files on demand
#    dist          - builds a zip file for distribution
#
############################################################################

## Paths to executables. Do not include options here.
## Modify these to suit your Coq installation, if necessary.

COQC = coqc
COQDEP = coqdep
COQDOC = coqdoc

## Paths for ott and lngen.

OTT = ott
LNGEN = ../../lngen

## Flags to lngen.  Mainly for --coq-admitted.

LNGENFLAGS = ## --coq-admitted

## Include directories, one per line.

INCDIRS = \
	. \
	metatheory \

## Directory where generated HTML documentation should go.

DOCDIR = html

## List of files that are processed by LNgen.

LNGEN_FILES = \
	Unbound \

## List of other files that should be compiled.

FILES = \

## Lists calculated from the above.

VFILES = \
	$(foreach i, $(LNGEN_FILES), $(i)_inf.v $(i)_ott.v) \
	$(foreach i, $(FILES), $(i).v) \

VOFILES  = $(VFILES:.v=.vo)

INCFLAGS = $(foreach i, $(INCDIRS), -I $(i))

############################################################################

.PHONY: all clean coq dist doc documentation force
.SUFFIXES: .v .vo

all: coq

coq: $(VOFILES)

doc:
	+make documentation

documentation: $(DOCDIR) $(VOFILES)
	$(COQDOC) -g --quiet --noindex --html -d $(DOCDIR) $(VFILES)
	cp -f custom.css $(DOCDIR)/coqdoc.css

clean:
	rm -f *.vo *.glob *.cmi *.cmx *.o
	rm -rf $(DOCDIR)

force:
	touch *.ott
	+make

############################################################################

%.vo: %.v Makefile
	$(COQC) -q $(INCFLAGS) $<

%_ott.v: %.ott
	$(OTT) -o $*_ott.v  -i $*.ott

%_inf.v: %.ott $(LNGEN) Makefile
	$(LNGEN) $(LNGENFLAGS) --coq $*_inf.v --coq-ott $*_ott --coq-loadpath metatheory $*.ott

$(DOCDIR):
	mkdir -p $(DOCDIR)

############################################################################

.depend: $(VFILES) Makefile
	$(COQDEP) $(INCFLAGS) $(VFILES) > .depend

include .depend
