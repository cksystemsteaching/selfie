Since there is no unit test system of any kind here, the test_arg_setter.py script
will print "all tests passed" if all its tests succeed.

### Test setup:

To test the arg_setter module, copy the current arg_setter.py from the parent
directory to the tests directory, then run:

python3 test_arg_setter.py

To test the full functionality of the arg_setter, run the following:

(from the selfie directory)

1. ``make webassembly``
2. ``python3 webassembly-resources/wasm-tools/arg_setter.py -c selfie.c -o test``
3. ``firefox selfie.html`` (or any other Browser with webassembly support)

This should compile selfie.c into a file called test that will be downloaded
to your Browser's download directory.

you can also run:

``python3 webassembly-resources/wasm-tools/arg_setter.py -c selfie.c -o test1 -s test2``

as the second command, which will produce a binary file called test1 and an assembly file called test2
and download each.