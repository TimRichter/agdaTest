#!/bin/bash

filename=$1

if [ -f /tmp/$filename ]; then
   rm /tmp/$filename;
fi

echo $filename | /home/tim/projects/TimRichter/agdaTest/TestIO3 > /tmp/$filename

mv /tmp/$filename $filename

