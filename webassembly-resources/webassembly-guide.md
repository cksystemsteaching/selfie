# This file contains general information about the webassembly development workflow

## Requirements

1. emscripten 1.38.6 or higher
  * To use emscripten, add its binaries to your path or use the source command to set up the environment variables before each session, i.e.:
``source ~/emsdk/emsdk_env.sh``
  * The Makefile contains a target(``webassembly``) which compiles selfie.c to selfie.wasm, generates the required javascript and creates a selfie.html file with the selfie.c source code preloaded into the Browser's file system
2. Browser (Firefox, Chrome, Edge or Safari) or node.js (only Browser use is covered in this guide)
  * The Browser acts as the environment in which your program executes
3. python3.5+ (recommended)

## General workflow

Files are compiled into a html file using the emscripten compiler (emcc) and can be used in the same manner as gcc:
```
emcc selfie.c -o selfie.html
```

If a file will be used by the program, it needs to be preloaded into the Browser's file system

```
emcc selfie.c -o selfie.html --preload-file selfie.c
```

Many compiler flags may be used when compiling with emcc. An example of this can be found in the Makefile (target webassembly).
Setting up command line arguments for the compiled code is done by modifying the html file.
For example, to get the equivalent command for:

```
./selfie -c selfie.c -m 4
```

The Module's arguments need to be set to this:
```
arguments: ["-c","selfie.c","-m","4"],
```
Note that we omit the program name in this case, as it is hardcoded within emscripten to "this.program".

The relevant code excerpt from selfie.html, after setting the arguments:
```
var Module = {
    arguments: ["-c","selfie.c","-m","4"],
    preRun: [],
```

The python script argument_setter.py in the wasm-tools may be used to make this
more convenient.

Using the argument_setter.py script the arguments can be set from the command line like this:
```
python3 argument_setter.py selfie.html -c selfie.c -m 4
```

In order to access the file system, it must be exported when compiling the code by adding:
```
-s EXTRA_EXPORTED_RUNTIME_METHODS='["FS"]'
```
See the Makefile target webassembly for an example of this

### Use case: Compiling selfie.c on mipster
1. make webassembly
2. python3 argument_setter.py -c selfie.c -m 2
3. firefox selfie.html

### Use case: Compiling selfie.c and downloading produced binary

The Browser sandbox does not allow directly accessing the local file system.
We can avoid this restriction by setting up an automatic download of our produced file(s).

This is code from an unmodified emscripten generated html file:
```
<script type='text/javascript'>
  var statusElement = document.getElementById('status');
  var progressElement = document.getElementById('progress');
  var spinnerElement = document.getElementById('spinner');

  var Module = {
    arguments: [],
    preRun: [],
    postRun: [],
    print: (function() {
```
Here is how to modify this code to set up an automatic download of the produced binary:

```
<script type='text/javascript'>
  var statusElement = document.getElementById('status');
  var progressElement = document.getElementById('progress');
  var spinnerElement = document.getElementById('spinner');

  // creating a hidden link we will .click() later to automatically download
  var hiddenLink = document.createElement("a");
  document.body.appendChild(hiddenLink);
  hiddenLink.style = "display: none";

  var Module = {
    arguments: ["-c","selfie.c","-o","selfie_web"],
    preRun: [],
    postRun: (function() {
      var downloadName = "selfie_web";

      // this chmod prevents file permission errors
      Module.FS.chmod("selfie_web", 777);
      // the buffer contains the raw bytes
      var bytes = Module.FS.readFile("selfie32web").buffer;
      // create a Blob out of our bytes, MIME type octet/stream
      var blob = new Blob([bytes], {type: 'octet/stream'});

      url = window.URL.createObjectURL(blob);

      // set the link to the new URLm, set the download name and click it
      hiddenLink.href = url;
      hiddenLink.download = downloadName;
      hiddenLink.click();

      // revoke URL after we are done using it
      window.URL.revokeObjectURL(url);
    }),
    print: (function() {
```

1. make webassembly
2. python3 argument_setter.py -c selfie.c -o selfie_web
3. Modify the selfie.html as shown above
4. firefox selfie.html


We can also download multiple produced files by setting up a download for each file.

The relevant code may look like this:

```
    postRun: (function() {
      // Setup for file_1
      Module.FS.chmod("file_1", 777);
      var bytes = Module.FS.readFile("file_1").buffer;
      var blob = new Blob([bytes], {type: 'octet/stream'});

      url = window.URL.createObjectURL(blob);

      hiddenLink.href = url;
      hiddenLink.download = "file_1";
      hiddenLink.click();

      window.URL.revokeObjectURL(url);

      // Setup for file_2
      Module.FS.chmod("file_2", 777);
      var bytes = Module.FS.readFile("file_2").buffer;
      var blob = new Blob([bytes], {type: 'octet/stream'});

      url = window.URL.createObjectURL(blob);

      hiddenLink.href = url;
      hiddenLink.download = "file_2";
      hiddenLink.click();

      window.URL.revokeObjectURL(url);

      // etc.
```
Where file_1 and file_2 were produced by our program and were saved to the Browser's file system.

### Status
As of the creation of this document, self compilation, self hosting and the creation of assembly and binary files
in a Browser (Firefox 64.0) work.

Loading preloaded files with the -l flag does not work, since the file descriptor is invalid with the existing flag.