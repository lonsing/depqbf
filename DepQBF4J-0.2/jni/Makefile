LPATH=-L.
CFLAGS=-Wextra -Wall -Wno-unused -pedantic -std=c99 -DNDEBUG -O3 
#JAVA_HOME=/usr/lib/jvm/java-6-sun-1.6.0.26
JAVAC=/usr/bin/javac
JAVAH=/usr/bin/javah
OBJECTS=DepQBF4J.o
LIBDEPQBF4J=libdepqbf4j.so
LIBQDPLL=libqdpll.a
JAVA_PACKAGE=depqbf4j
JAVA_PATH_PREFIX=../src
JAVA_INTERFACE_CLASS=$(JAVA_PATH_PREFIX)/$(JAVA_PACKAGE)/DepQBF4J.class
JAVA_INTERFACE_SOURCE=$(JAVA_PATH_PREFIX)/$(JAVA_PACKAGE)/DepQBF4J.java

MAJOR=1
MINOR=0
VERSION=$(MAJOR).$(MINOR)

.PHONY: clean cleanall

$(LIBDEPQBF4J): $(LIBDEPQBF4J).$(VERSION)
	ln -fs $@.$(VERSION) $@

$(JAVA_INTERFACE_CLASS): $(JAVA_INTERFACE_SOURCE)
	$(MAKE) -C $(JAVA_PATH_PREFIX)/$(JAVA_PACKAGE)/

depqbf4j_DepQBF4J.h: $(JAVA_INTERFACE_CLASS)
	$(JAVAH) -classpath $(JAVA_PATH_PREFIX)/ $(JAVA_PACKAGE).DepQBF4J

$(LIBQDPLL):
	./compile-lib-depqbf4java.sh

DepQBF4J.o: DepQBF4J.c depqbf4j_DepQBF4J.h
	$(CC) $(CFLAGS) -fPIC -c DepQBF4J.c -I $(JAVA_HOME)/include -I $(JAVA_HOME)/include/linux

$(LIBDEPQBF4J).$(VERSION): $(OBJECTS) $(LIBQDPLL)
	$(CC) $(CFLAGS) $(OBJECTS) $(LIBQDPLL) -shared -Wl,-soname,depqbf4j.so.$(MAJOR) -o $@

clean:
	rm -f libqdpll.a DepQBF4J.o depqbf4j_DepQBF4J.h $(LIBDEPQBF4J).$(VERSION) $(LIBDEPQBF4J)

cleanall: clean
	$(MAKE) -C $(JAVA_PATH_PREFIX)/$(JAVA_PACKAGE)/ clean
