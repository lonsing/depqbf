#!/bin/bash

cd ../../
cd nenofex
echo "D4J libs: compiling Nenofex"
cc -std=c99 -Wextra -Wall -Wno-unused -O3 -DNDEBUG -pedantic -fPIC -c stack.c -o D4Jstack.fpico
cc -std=c99 -Wextra -Wall -Wno-unused -O3 -DNDEBUG -pedantic -fPIC -c queue.c -o D4Jqueue.fpico
cc -std=c99 -Wextra -Wall -Wno-unused -O3 -DNDEBUG -pedantic -fPIC -c mem.c -o D4Jmem.fpico
cc -std=c99 -Wextra -Wall -Wno-unused -O3 -DNDEBUG -pedantic -fPIC -c atpg.c -o D4Jatpg.fpico
cc -std=c99 -Wextra -Wall -Wno-unused -O3 -DNDEBUG -pedantic -fPIC -c nenofex.c -o D4Jnenofex.fpico

cd ../
cd picosat
echo "D4J libs: compiling PicoSAT"
cc -DNDEBUG -O3 -fPIC -c picosat.c -o D4Jpicosat.fpico

echo "D4J libs: compiling DepQBF"
cd ../
cc -Wextra -Wall -Wno-unused -pedantic -std=c99 -DNDEBUG -O3 -fPIC -c qdpll.c -o D4Jqdpll.fpico
cc -Wextra -Wall -Wno-unused -pedantic -std=c99 -DNDEBUG -O3 -fPIC -c qdpll_pqueue.c -o D4Jqdpll_pqueue.fpico
cc -Wextra -Wall -Wno-unused -pedantic -std=c99 -DNDEBUG -O3 -fPIC -c qdpll_mem.c -o D4Jqdpll_mem.fpico
cc -Wextra -Wall -Wno-unused -pedantic -std=c99 -DNDEBUG -O3 -fPIC -c qdpll_dep_man_qdag.c -o D4Jqdpll_dep_man_qdag.fpico
cc -Wextra -Wall -Wno-unused -pedantic -std=c99 -DNDEBUG -O3 -fPIC -c qdpll_dynamic_nenofex.c -o D4Jqdpll_dynamic_nenofex.fpico
ar rc D4Jlibqdpll.a D4Jqdpll.fpico D4Jqdpll_pqueue.fpico D4Jqdpll_mem.fpico D4Jqdpll_dep_man_qdag.fpico D4Jqdpll_dynamic_nenofex.fpico ./nenofex/D4Jstack.fpico ./nenofex/D4Jqueue.fpico ./nenofex/D4Jmem.fpico ./nenofex/D4Jatpg.fpico ./nenofex/D4Jnenofex.fpico ./picosat/D4Jpicosat.fpico
ranlib D4Jlibqdpll.a
cp D4Jlibqdpll.a DepQBF4J-0.2/jni/libqdpll.a

rm D4J*
rm nenofex/D4J*
rm picosat/D4J*
