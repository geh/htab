#!/bin/bash

HTABPATH="../bin/htab"    # path to HTab
UNSATPATH="sat"              # directory where examples are

for file in `ls ${UNSATPATH}/*.frm`;
do echo $file;${HTABPATH} -f $file $1 $2 $3 $4;
done


