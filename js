#!/bin/sh

WD=$(cd $(dirname $0); pwd)
CP=$(cat $WD/.classpath)
OPTS=$(cat $WD/.sbtopts)
LOG=-Dlogger.file=$WD/src/main/resources/logback.xml

scala -cp $CP $LOG $LIB $OPTS sc.js.machine.Main "$@"
