all:
  gcc -g3 -o basic-api-example basic-api-example.c -L.. -lqdpll
doc:
  pydoc -w ./DepQBF.py
test:
  python ./DepQBF.py
  #python -m doctest DepQBF.py


with_stats:
	sed s'/\#define COMPUTE_STATS 0/\#define COMPUTE_STATS 1/' ../qdpll_config.h 
	sed s'/\#define COMPUTE_TIMES 0/\#define COMPUTE_TIMES 1/' ../qdpll_config.h 
