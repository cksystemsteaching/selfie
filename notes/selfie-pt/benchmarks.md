# Runtimes for `make all`
The runtimes are the output of `time make all` on an Arch Linux (Kernel 5.4.x or 5.5.x (can't remember) for "`master`", "`tree-pt`" and "`tree-pt` with optimized index calculations" and 5.6.3 for "`tree-pt` with root node caching" and "`tree-pt` with optimized index calculations and root node caching") machine with an Intel Core i5 4670k (not overclocked).

## `master`
```
real    14m14.499s
user    11m29.593s
sys     0m44.828s
```

## `tree-pt`
```
real     45m25.995s
user     42m2.712s
sys      0m49.508s
```

## `tree-pt` with optimized index calculations
```
real    37m13.655s
user    33m35.455s
sys     0m53.421s
```

## `tree-pt` with root node caching
```
real    20m10.784s
user    17m6.642s
sys     0m45.730s
```

## `tree-pt` with optimized index calculations and root node caching
```
real    15m3.947s
user    12m5.389s
sys     0m46.760s
```
