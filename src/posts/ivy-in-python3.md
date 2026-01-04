---
layout: post.njk
title: "Notes on setting up Ivy in Python 3"
date: 2022-04-17T14:18:48-05:00
tags: [post, ivy, verification]
excerpt: ""
---

I use [Ivy](http://microsoft.github.io/ivy/) as part of my day-to-day research.
It's a cool language with lots of nice properties, but initially setting it up
on a modern machine can be a bit tricky.  It's written in Python 2, which is no
longer easily installable on modern systems, and requires a specific old
version of Z3.  As a result, it becomes tedious to juggle Python interpreter and
dependency versions if you need Python and Z3 for other stuff on the same machine.

I spent some time a few years ago porting IVy to run under Python 3.  I've also
shown a bunch of people in my lab how to get it running in a local Python
virtual environment, which means that dependencies (in particular, Ivy's
ancient fork of the Z3 solver) don't pollute your wider system. However, I keep
losing my notes about what steps to take so hopefully this is the last time I
have to reconstruct them!

## 0. Install Python3 and venv if you don't already have it

```
$ # Ubuntu/PopOS/etc...
$ sudo apt-get install python3.10-venv

$ # MacOS...
$ brew install python@3.10
```

## 1. Check out the Python 3 Ivy fork and set up your virtual environment

```
$ git clone git@github.com:dijkstracula/ivy.git --recurse-submodules
$ cd ivy
$ git checkout nathan/python3_port
Branch 'nathan/python3_port' set up to track remote branch 'nathan/python3_port' from 'origin'.
Switched to a new branch 'nathan/python3_port'

$ python3 -m venv ./venv
$ ls venv                  
bin  include  lib  lib64  pyvenv.cfg
```

Enter the virtual environment, which you'll have to do each time you want to
run Ivy, and ensure that your PATH points `python` into your venv.  

```
$ source ./venv/bin/activate
(venv) $ which python
/home/ntaylor/code/ivy/venv/bin/python
(venv) $ python --version
Python 3.10.12
(venv) $
```

By contrast, you likely do not have a valid z3 installation (or if you do, it's
installed globally by you, and not the very specific version we need here.)

```
(venv) $ which z3
z3 not found
(venv) $ python -c 'import z3; print(z3.get_version())'
Traceback (most recent call last):
  File "<stdin>", line 1, in <module>
ModuleNotFoundError: No module named 'z3'
(venv) $
```

## 2. Build and install the z3 fork.

The only dependency we care about is Z3 (the instructions for picotls are
probably not fundamentally different if you are doing TLS protocol
verification).  We are going to compile Z3 in order to install it locally
within our virtual environment as opposed to a global installation in /usr (or
/opt, etc...)

IVy comes with a `build_submodules.py` script that normally automates this;
however, we need to give a different `--prefix` to the Z3 configure script so
we'll run the command manually.


```
(venv) $ cd submodules/z3 
(venv) $ python scripts/mk_make.py --prefix=$VIRTUAL_ENV --python
  ...
  Python pkg dir: /home/ntaylor/code/ivy/venv/lib/python3.10/site-packages
  Python version: 3.10
  ...
  Z3 was successfully built.
  ...
  Use the following command to install Z3 at prefix /home/ntaylor/code/ivy/venv.
    sudo make install
(venv) $
```

Ensure that the output of running the configure script points into your virtual
environment.  Because we are installing Z3 locally, we do not need to run `make
install` with `sudo`.

```
(venv) $ cd build; make -j8 install
  ...
  Z3 was successfully installed.
(venv) $
```

You can now confirm that the Z3 binary, on your $PATH, is the one inside your
virtual environment; and, that version 4.7.1 can be loaded from your Python
interpreter:

```
(venv) $ which z3
/home/ntaylor/code/ivy/venv/bin/z3
(venv) $ python3 -c 'import z3; print(z3.get_version())'
(4, 7, 1, 0)
(venv) $ 
```

## 3. Install Ivy into your virtual environment

As I often want to modify the Ivy source myself, I do a `develop` installation
so that I can modify Ivy without needing to constantly repackage and reinstall
it.

```
(venv) $ cd ../../../ # back to the root Z3 directory
(venv) $ python setup.py develop
  ...
  Creating /home/ntaylor/code/ivy/venv/lib/python3.10/site-packages/ms-ivy.egg-link (link to .)
  ...
  Installed /home/ntaylor/code/ivy
  ...
  Finished processing dependencies for ms-ivy==1.8.23
(venv) $ which ivyc
/home/ntaylor/code/ivy/venv/bin/ivyc
(venv) $ 
```

And now we can test compiling an Ivy program!

```
(venv) $ cd /tmp/   
(venv) $ ivyc target=test foo.ivy
g++ -Wno-parentheses-equality  -std=c++11  -I /home/ntaylor/code/ivy/ivy/include -L /home/ntaylor/code/ivy/ivy/lib -Xlinker -rpath -Xlinker /home/ntaylor/code/ivy/ivy/lib -I /home/ntaylor/code/ivy/venv/lib/python3.10/site-packages/z3/include -L /home/ntaylor/code/ivy/venv/lib/python3.10/site-packages/z3/lib -Xlinker -rpath -Xlinker /home/ntaylor/code/ivy/venv/lib/python3.10/site-packages/z3/lib -I /home/ntaylor/code/ivy/venv/include -L /home/ntaylor/code/ivy/venv/lib -Xlinker -rpath -Xlinker /home/ntaylor/code/ivy/venv/lib -g -o foo foo.cpp -lz3 -pthread
(venv) $ ivy_launch foo
  ...
```

Happy proving!
