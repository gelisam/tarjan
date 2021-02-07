#!/bin/bash
set -e

clear
agda --compile \
  --library standard-library \
  --include-path src \
  src/Main.agda
