#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp.rkt")
(require "compiler-r1.rkt")

(debug-level 2)

(interp-tests "r1 compiler" #f r1-passes interp-scheme "r1" (range 1 22))
(compiler-tests "r1 compiler" #f r1-passes "r1" (range 1 22))
(compiler-tests "r1 compiler" #f r1-passes "r1a" (range 1 9))
(display "tests passed!") (newline)
