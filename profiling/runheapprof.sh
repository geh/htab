#!/bin/bash

for file in `ls prof/*.cnf`;
do echo $file;../bin/htabprof -t 30 -f $file $1 $2 $3 $4 +RTS -hc -RTS; mv htabprof.hp $file.hp;
done

