#!/bin/bash

if [ ! -d picosat ]
then
  echo "Downloading picosat version 960"
  wget http://fmv.jku.at/picosat/picosat-960.tar.gz
  tar -xvzf picosat-960.tar.gz
  mv picosat-960 picosat
else
  echo "Found directory 'picosat'"
fi

cd picosat
./configure
make
cd ..

if [ ! -d nenofex ]
then
    echo "Downloading nenofex version 1.1"
    wget https://github.com/lonsing/nenofex/archive/version-1.1.tar.gz
    tar -xvzf version-1.1.tar.gz
    mv nenofex-version-1.1 nenofex
else
    echo "Found directory 'nenofex'"
fi

cd nenofex
make
cd ..

# Compile DepQBF
make
