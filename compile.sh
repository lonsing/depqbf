#!/bin/bash

# Run './compile.sh' to compile DepQBF including Bloqqer library.
# Run './compile.sh nobloqqer' to compile DepQBF without linking
#  Bloqqer library. However, this may have a negative influence on the
#  performance

NOBLOQQER=0

if [ $# -eq 1 ]
then
    if [ "$1" = "nobloqqer" ]
    then
	NOBLOQQER=1
    fi
fi

if [ ! -d picosat-960 ]
then
  echo "Downloading picosat version 960"
  wget http://fmv.jku.at/picosat/picosat-960.tar.gz
  tar -xvzf picosat-960.tar.gz
else
  echo "Found picosat directory 'picosat-960'"
fi

cd picosat-960
./configure
make
cd ..

if ((!$NOBLOQQER))
then
    if [ ! -d bloqqer35 ]
    then
	echo "Downloading bloqqer version 35"
	wget http://fmv.jku.at/bloqqer/bloqqer-035-f899eab-141029.tar.gz
	tar -xvzf bloqqer-035-f899eab-141029.tar.gz
	mv bloqqer-035-f899eab-141029 bloqqer35
    else
	echo "Found bloqqer directory 'bloqqer35'"
    fi
    
    #fix memory error in bloqqer35 (error has been fixed in more recent version 37 of bloqqer already)
    patch bloqqer35/bloqqer.c bloqqer35-fix.patch
    cd bloqqer35
    ./configure
    make
    make libbloqqer.a
    cd ..
fi

if (($NOBLOQQER))
then
    echo "Modifying DepQBF makefile to avoid linking Bloqqer library."
    ls makefile-original 2>/dev/null
    if (($?))
    then
	# backup original makefile 
	cp makefile makefile-original
    fi
    #cp makefile makefile-original
    sed '/LFLAGS/s/-L.\/bloqqer35//; /LFLAGS/s/-lbloqqer//; /CFLAGS=\(.*\)/s/$/ -DNBLOQQER/; s/.\/bloqqer35\/libbloqqer.o//' makefile-original > makefile
else
    ls makefile-original 2>/dev/null
    if ((!$?))
    then
	# restore original makefile 
	cp makefile-original makefile
    fi
fi

# Compile DepQBF
make
