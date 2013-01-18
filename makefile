#CFLAGS=-Wextra -Wall -Wno-unused -pedantic -std=c99 -DNDEBUG -O3 
CFLAGS=-Wextra -Wall -Wno-unused -pedantic -std=c99 -DNDEBUG -O3 -static
#CFLAGS=-Wextra -Wall -Wno-unused -pedantic -std=c99 -g3 -static
#CFLAGS=-Wextra -Wall -Wno-unused -pedantic -std=c99 -DNDEBUG -g3 -pg -fprofile-arcs -ftest-coverage -static
OBJECTS=qdpll_main.o qdpll_app.o qdpll.o qdpll_mem.o qdpll_dep_man_qdag.o

depqbf: qdpll_main.o qdpll_app.o libqdpll.a
	$(CC) $(CFLAGS) qdpll_main.o qdpll_app.o -L. -lqdpll -o depqbf

qdpll_main.o: qdpll_main.c qdpll.h
	$(CC) $(CFLAGS) -c qdpll_main.c

qdpll_app.o: qdpll_app.c qdpll_internals.h qdpll.h qdpll_exit.h qdpll_config.h
	$(CC) $(CFLAGS) -c qdpll_app.c

qdpll.o: qdpll.c qdpll_internals.h qdpll.h qdpll_mem.h qdpll_pcnf.h qdpll_exit.h \
	 qdpll_stack.h qdpll_dep_man_generic.h qdpll_dep_man_qdag.h \
	 qdpll_config.h qdpll_dep_man_qdag_types.h
	$(CC) $(CFLAGS) -c qdpll.c

qdpll_mem.o: qdpll_mem.c qdpll_mem.h qdpll_exit.h
	$(CC) $(CFLAGS) -c qdpll_mem.c

qdpll_dep_man_qdag.o: qdpll_dep_man_qdag.c qdpll_pcnf.h qdpll_exit.h \
	              qdpll_dep_man_generic.h qdpll_dep_man_qdag.h qdpll_config.h \
		      qdpll.h qdpll_dep_man_qdag_types.h qdpll_stack.h \
		      qdpll_internals.h
	$(CC) $(CFLAGS) -c qdpll_dep_man_qdag.c

libqdpll.a: qdpll.o qdpll_mem.o qdpll_dep_man_qdag.o
	ar rc $@ qdpll.o qdpll_mem.o qdpll_dep_man_qdag.o
	ranlib $@


clean:
	rm -f *.a *.o *.gcno *.gcda *.gcov *~ gmon.out depqbf
