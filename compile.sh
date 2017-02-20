#!/bin/bash

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

if [ ! -d bloqqer35 ]
then
  echo "Downloading bloqqer version 35"
  wget http://fmv.jku.at/bloqqer/bloqqer-035-f899eab-141029.tar.gz
  tar -xvzf bloqqer-035-f899eab-141029.tar.gz
  mv bloqqer-035-f899eab-141029 bloqqer35
else
  echo "Found bloqqer directory 'bloqqer35'"
fi

cd bloqqer35
./configure
make
make libbloqqer.a
cd ..

make
