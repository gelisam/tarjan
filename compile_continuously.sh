#!/bin/bash
set -e

./compile.sh || true
fswatcher --throttle 300 --path src/MonadClasses.agda ./compile.sh
