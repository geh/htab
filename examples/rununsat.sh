#!/bin/bash

UNSATPATH="unsat"            # directory where examples are

type htab # print which path we are using

for file in `ls ${UNSATPATH}/*.frm`;
do echo $file;htab -f $file $1 $2 $3 $4;
done

