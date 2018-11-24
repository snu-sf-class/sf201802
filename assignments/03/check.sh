#!/usr/bin/env bash

if [ "$#" -gt 1 ]; then
  echo "check.sh"
  echo "check.sh <problem #(ex:01)>"
  exit 1
fi

# Get the directory this script resides in
THISDIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"
if [ "$#" -eq 0 ]; then
  PROBNUM=
else
  PROBNUM=$1
fi

function check_keyword() {
    echo "$1:"
    if [ "$PROBNUM" == "" ]; then
      grep $1 $THISDIR/P??.v
      local res=$?
    else
      grep $1 $THISDIR/P${PROBNUM}.v
      local res=$?
    fi
    echo ""
    return $res
}

res=1
for keyword in `cat $THISDIR/forbidden.txt`; do
    check_keyword ${keyword}
    r=$?
    if [ "$r" -eq 0 ]; then
      # found!
      res=$r
    fi
done
exit $res

