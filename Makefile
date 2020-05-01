COQMKFILENAME=CoqSrc.mk

all: coq

#_CoqProject:
#	{ echo "-Q metalib/Metalib Top.Metalib" ; echo "-Q . Top" ; ls *.v ; } > $@

$(COQMKFILENAME): Makefile _CoqProject
	coq_makefile -f _CoqProject -o $(COQMKFILENAME)

metalib/Metalib/%.vo: metalib/Metalib/%.v
	{ cd metalib/Metalib ; make all ; }

coq: $(COQMKFILENAME) metalib/Metalib/Metatheory.vo metalib/Metalib/LibLNgen.vo
	{ cd metalib/Metalib ; make all ; }
	$(MAKE) -f $(COQMKFILENAME)

