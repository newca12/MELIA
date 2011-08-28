## Makefile for the MELIA prover
## make without arguments results in the executable shell script target/scala/melia 
## which can be copied anywhere.
## Its execution requires an installed scala runtime, i.e. 
## the "scala" program must be in the search path.
##
## Alternatively, "make java-jar" results in the executable shell script target/java/melia 
## which uses the java runtime (hence no scala runtime is required)

## Author: Peter Baumgartner, NICTA


## Set SCALA_HOME appropriately
SCALA_HOME = /usr/local/scala/

## pick one
## "Fast" scala compiler
SCALAC = fsc
## SCALAC = fsc -make:changed
## SCALAC = scalac

## Nothing should be serviced beyond this point

MAIN = Main
classes = classes
SRC_DIR = src

HERE = $(PWD)

SCALAC_OPTS = -encoding utf8
# SCALAC_OPTS = -g:vars -encoding utf8 -deprecation
# SCALAC_OPTS = -g:notailcalls 
# SCALAC_OPTS = 

SCALA_OPTS = -Dfile.encoding=UTF-8
# SCALA_OPTS = 

all: scala-jar

compile:
	$(SCALAC) -d classes $(SCALAC_OPTS) $(SRC_DIR)/*.scala

java-jar: compile java-MANIFEST
	( cd classes; \
	  jar xvf $(SCALA_HOME)/lib/scala-library.jar; \
	  jar -cfm ../target/java/MELIA.jar ../target/java/MANIFEST.MF * ; \
	   rm -rf scala )
	( cd target/java; \
	  echo '#!/bin/sh' > melia; \
	  echo 'java -Dfile.encoding=UTF-8 -jar $(HERE)/target/java/MELIA.jar $$*' >> melia ; \
	  echo '#' >> melia; \
	  chmod 755 melia )

java-MANIFEST:
	( cd target/java/ ;\
	  echo "Main-Class: $(MAIN)" > MANIFEST.MF )


scala-jar: compile scala-MANIFEST
	( cd classes; jar -cfm ../target/scala/MELIA.jar ../target/scala/MANIFEST.MF *.* )
	( cd target/scala; \
	  echo '#!/bin/sh' > melia; \
	  echo 'scala -Dfile.encoding=UTF-8 $(HERE)/target/scala/MELIA.jar $$*' >> melia ; \
	  echo '#' >> melia; \
	  chmod 755 melia )


scala-MANIFEST:
	( cd target/scala/ ;\
	  echo "Main-Class: $(MAIN)" > MANIFEST.MF )


%.run: compile
	scala $(SCALA_OPTS) -classpath classes $(MAIN) $*

debug: compile
	jdb -classpath classes:$(SCALA_HOME)/lib/scala-library.jar \
	-sourcepath $(SRC_DIR) \
	-launch $(MAIN) $(ARG)

tar: clean
	( cd .. ; tar zcvf MELIA.tar.gz MELIA/* )

clean:
	rm -f target/java/*
	rm -f target/scala/*
	rm -f classes/*.*

