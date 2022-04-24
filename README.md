## Overview

This repository is based on my PhD thesis [Formalising a real-time coordination model](http://www.tara.tcd.ie/bitstream/handle/2262/77596/Bhandal%2c%20Colm_TCD-SCSS-PHD-2014-08.pdf?sequence=1&isAllowed=y). In that thesis, I define a process algebgra for the description of hybrid systems with the ability to communicate over wireless networks and also perform internal computations. The process algebra is "multi-tiered", meaning it is defined in several tiers. Roughly, it can be thought of as an "inner" language running the software and an "outer" language encoding nodes which can move around in space and communicate over a wireless network. The separation of the language into components like this allows a separation-of concers in defining aspects of the system which are really orthogonal. Also, by defining the language separately to the protocol, the language lends itself for reuse i.e. specifying other protocols in similar environments.

Using the multi-tiered language I define, I write a protocol which builds upon the work of [Bouroche, 2007](https://www.scss.tcd.ie/publications/theses/phd/TCD-SCSS-PHD-2007-07.pdf). Then, I prove a safety condition of that protocol. Safety is an abstract concept defined in terms of modes and distances; concrete instantiations of this protocol must specify what the modes are and what the minimum distance of separation is for any pair of modes.

The proof found in my thesis has been formalised in Coq. However, some of the results in Coq are not proved completely. Those are marked as ``Admitted``, meaning we are assuming the results to be true without proof. There is more information on this in the future work section below.

## Warning

In its current state, this code is not recommended for inclusion in any downstream projects. The code contains many ``Admitted`` results which are effectively axioms, and thus there is no guarantee of consistency. If various modules of the code were refactored to separate repos e.g. ``StandardResults.v``, then those would be fine for reuse. But as of the time of writing, this is not planned.

## Building the Project

### Prerequisites

[Install Coq with OPAM](https://coq.inria.fr/opam-using.html). Unfortunately this is not supported on Windows but there is a workaround.

### Windows Workaround

The idea is to run install and use Coq through WSL and then expose any graphical applications through VcXsrv (since WSL doesn't have a UI). An excellent outline of how to do this is found at [CoqWSL](https://lemonidas.github.io/CoqWSL.html).

### Local Build

There is a top-level ``Makefile`` in the root directory of this repository. To build the Coq project just open a terminal in that directory and run:

``make``

This ultimately ends up calling Coq's ``coq_makefile`` command, if necessary, to make an intermediary make file called ``Makefile.coq`` and then the top-level target of _that_ make file does all the heavy lifting, converting source ``.v`` files into output ``.vo`` files.

### Cleaning

You may want to clean the project. All files cleaned are not checked into this repo - they are produced by various make/build commands. You can either clean the compiled files, the "Coq makefiles", or both. To clean the compiled files:

``make clean-compiled``

To clean the auto-generated make files, run:

``make clean-make``

To clean everything, just do:

``make clean``

## Repo Roadmap

All source ``.v`` files can be found in the repo ``src``. The folder ``Extras`` contains content which I did not write but needed to include - this was not available through standard import.

### Top-Level Result

The top-level safety condition is proved in [Main.v](https://github.com/ColmBhandal/PhD-Formalilsing-Comhordu/blob/develop/Main.v). The top-level Theorem is called ``safety``:

``Theorem safety (n : Network) : reachableNet n -> safe n.``

### Software Language & Protocol

The software component of the language is the language in which the protocol itself is written. It is a language with a flavour similar to [CCS](https://en.wikipedia.org/wiki/Calculus_of_communicating_systems#:~:text=The%20calculus%20of%20communicating%20systems,communications%20between%20exactly%20two%20participants.) or [CBS](https://link.springer.com/content/pdf/10.1007%2F3-540-53982-4_19.pdf). The language and protocol are defined in [SoftwareLanguage.v](https://github.com/ColmBhandal/PhD-Formalilsing-Comhordu/blob/develop/SoftwareLanguage.v). The language gives a discrete semantics - to represent computations, as well as a "delay" semantics - to capture the behaviour of terms in the presence of continuous time.

### Other Modules

There are a number of other modules for defining other components of the language and proving results. These can be explored through the documentation comments inline in the files themselves or the CoqDoc - see CoqDoc section for more. The [PhD thesis](http://www.tara.tcd.ie/bitstream/handle/2262/77596/Bhandal%2c%20Colm_TCD-SCSS-PHD-2014-08.pdf?sequence=1&isAllowed=y) itself also contains a roadmap of the repo, although it may go out of date if the repo evolves. 

## CoqDoc

### Online DocDoc

The code is pretty-printed online. There are two versions - one with proofs, one without. Below are links to the table of contents for each:
 1. [Without Proofs](https://colmbhandal.github.io/PhD-Comhordu-CoqDoc/light/toc.html)
 2. [With Proofs](https://colmbhandal.github.io/PhD-Comhordu-CoqDoc/verbose/toc.html)

### Building the CoqDoc Locally

CoqDoc is pretty-printed documentation of Coq code. For more info, see [Documenting Files...](https://coq.inria.fr/refman/using/tools/coqdoc.html)

The directory ``CoqDoc/`` is ignored via the ``.gitignore`` file and so it is recommended to build any CoqDoc locally here. There are many arguments you can pass to CoqDoc e.g. you can choose to omit proofs; for a full explanation of those arguments just run ``coqdoc --help``. Here are just two options that I think are useful:

 1. To build standard HTML docs, including full proofs, into a ``verbose`` directory, use: ``coqdoc --html -d "CoqDoc/verbose" src/*.v --no-index --toc``
 1. To build light HTML, without proofs, use: ``coqdoc --html -g -d "CoqDoc/light" src/*.v --no-index --toc``

Note: the ``Index.html`` file renders with a bunch of broken links so I ignore it with ``--no-index`` and instead use a table of contents file as the entry point, using ``--toc``. This could probably be improved in future.

You can also build the CoqDoc via ``make`` with:

``make coqdoc``

This will build both a light and verbose version of the CoqDoc as specified above.

## Potential Improvements

I originally started to entitle this section "Future Work" but that would be misleading: I do not at the moment plan to carry out any future updates to this repository. That could change though, or others may want to contribute, so for that reason I am documenting a number of potential improvements to this project. More or less, they are in order of priority, by my estimation.

 - All general-purpose results in ``StandardResults.v`` should be extracted from this repo and shared as a standalone library. However, when doing so, any results which already exist in other libraries should be removed, and their usage should be replaced with usage of the more standard results. Similar reasoning applies to ``GenTacs.v``, which contains mostly general-purose tactics.
 - Ideally, this project should be decomposed into a number of repos, to make it clear what the various components do and to better expose and document them for reuse. As an MVP, the language components should be separated to their own repo, with results proved about the language independent of the protocol. This would allow for reuse of the language. It may also yield some research papers e.g. a paper defining the language, proving some general properties e.g. non-Zenoness, showing some examples and example applications. Such a paper would be a modular extraction of the content of my PhD thesis in much the same manner as the extraction of repos from this one would modularise the code.
 - Once this project is decomposed into various repos, they should be published and made available for others to use.
 - Not all results in this project were proved in Coq. About 30% of the results were ``Admitted``. The file [coq_proj.pdf](https://github.com/ColmBhandal/PhD-Formalilsing-Comhordu/blob/develop/coq_proj.pdf) gives more detail on this. In particular, it outlines what needs to be done and how. It would be nice to prove everything completely, but strategically I think a better move would be to first decompose and better modularise the repo. It's unclear whether there is high demand for the proof of safety for this protocol itself, and unless/until there is I don't see much merit in completing a lengthy proof just for the sake of it.

More improvements are outlined in [Issues](https://github.com/ColmBhandal/PhD-Formalilsing-Comhordu/issues).

## Notes

These files were written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.
