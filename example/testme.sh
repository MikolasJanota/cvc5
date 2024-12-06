#!/bin/bash
#
# File:  t
# Author:  mikolas
# Created on:  Tue Nov 12 18:06:09 CET 2024
# Copyright (C) 2024, Mikolas Janota
#
#
# ./cvc5 --probgen-inst --dump-instantiations --produce-proof -t inst-alg-pt -t inst -t probgen ~/git/experiments/quantifiers/g.smt2
# ./cvc5 --probgen-inst  --dump-instantiations --produce-proof -t probgen -t inst-alg-pt ~/git/experiments/quantifiers/g.smt2 | tee /tmp/o
./cvc5 --probgen-inst --dump-instantiations --produce-proof -t probgen -t inst-alg-pt ~/git/experiments/quantifiers/g_skolem.smt2 | tee /tmp/o
