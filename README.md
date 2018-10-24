# Compiler for a fictional programming language
Supplementary repository for compiler course. 
An interpreter and X86-compiler 

## Building

Prerequisites: ocaml [http://ocaml.org], opam [http://opam.ocaml.org].

* `opam pin add GT https://github.com/dboulytchev/GT.git`
* `opam pin add ostap https://github.com/dboulytchev/ostap.git`
* `opam install ostap`
* `opam install GT`
* `eval $(opam config env)`
* To build the sources: `make` from the top project directory
* To test: `test.sh` from `regression` subfolder
* To compile: `src/rc.opt source_name.expr`

## Syntax example
Language is pretty simple but includes all the basic constructions such as loops, functions, procedures, arrays, strings, pattern matching.


### Fibonacci
```
fun fib (n) local r {
  if n <= 1
  then result := 1
  else
    fib (n-1);
    r := result;
    fib (n-2);
    result := result + r
  fi
}

n := read();

for i := n, i >= 1, i := i-1 do
  fib (i);
  write (i);
  write (result)
od
```

### Sum of the list
```
fun sum (x) {
  case x of
    `nil          -> return 0
  | `cons (x, tl) -> return x + sum (tl)
  esac
}

x := read ();

write (sum (`cons (100, `cons (200, `nil))))
```

### Buuble sort
```
fun sort (x) local i, j, y, n {
  n := x.length;
  
  if n == 0 then return x fi;
  
  for i := 0, i<n, i := i+1 do
    for j := i+1, j<n, j := j+1 do
      if x[j] < x[i] then
         y    := x[i];
	 x[i] := x[j];
	 x[j] := y
      fi
    od
  od;
  
  return x
}

n := read ();
x := [10, 9, 8, 7, 6, 5];

x := sort (x);

for i:=0, i<x.length, i:=i+1 do
  write (x[i])
od
```
