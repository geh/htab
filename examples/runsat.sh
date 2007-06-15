#!/bin/bash

HTABPATH="../bin/htab"    # path to HTab
UNSATPATH="sat"              # directory where examples are

for file in `ls ${UNSATPATH}/*.frm`;
do echo $file;${HTABPATH} -sb 0 -fc 0 -f $file $1 $2 $3 $4;
done


