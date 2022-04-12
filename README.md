## Overview

This repository is based on my PhD thesis [Formalising a real-time coordination model](http://www.tara.tcd.ie/handle/2262/77596). In that thesis, I define a process algebgra for the description of hybrid systems with the ability to communicate over wireless networks and also perform internal computations. The process algebra is "multi-tiered", meaning it is defined in several tiers. Roughly, it can be thought of as an "inner" language running the software and an "outer" language encoding nodes which can move around in space and communicate over a wireless network. The separation of the language into components like this allows a separation-of concers in defining aspects of the system which are really orthogonal. Also, by defining the language separately to the protocol, the language lends itself for reuse i.e. specifying other protocols in similar environments.

Using the multi-tiered language I define, I write a protocol which builds upon the work of [Bouroche, 2007](https://www.scss.tcd.ie/publications/theses/phd/TCD-SCSS-PHD-2007-07.pdf). Then, I prove a safety condition of that protocol. Safety is an abstract concept defined in terms of modes and distances; concrete instantiations of this protocol must specify what the modes are and what the minimum distance of separation is for any pair of modes.

The proof found in my thesis has been formalised in Coq. However, some of the results in Coq are not proved completely. Those are marked as ``Admitted``, meaning we are assuming the results to be true without proof. There is more information on this in the future work section below.

## Repo Roadmap

All source ``.v`` files can be found in the repo ``src``. The folder ``Extras`` contains content which I did not write but needed to include - this was not available through standard import.

### Top-Level Result

The top-level safety condition is proved in [Main.v](https://github.com/ColmBhandal/PhD-Formalilsing-Comhordu/blob/develop/Main.v). The top-level Theorem is called ``safety``:

``Theorem safety (n : Network) : reachableNet n -> safe n.``

### Software Language & Protocol

The software component of the language is the language in which the protocol itself is written. It is a language with a flavour similar to [CCS](https://en.wikipedia.org/wiki/Calculus_of_communicating_systems#:~:text=The%20calculus%20of%20communicating%20systems,communications%20between%20exactly%20two%20participants.) or [CBS](https://link.springer.com/content/pdf/10.1007%2F3-540-53982-4_19.pdf). The language and protocol are defined in [SoftwareLanguage.v](https://github.com/ColmBhandal/PhD-Formalilsing-Comhordu/blob/develop/SoftwareLanguage.v). The language gives a discrete semantics - to represent computations, as well as a "delay" semantics - to capture the behaviour of terms in the presence of continuous time.

### Other Modules

There are a number of other modules for defining other components of the language and proving results. These can be explored through the documentation comments inline in the files themselves. 

## Potential Improvements

 - Not all results in this project were proved in Coq. About 30% of the results were admitted. The [file coq_proj.pdf](https://github.com/ColmBhandal/PhD-Formalilsing-Comhordu/blob/develop/coq_proj.pdf) gives more detail on this. In particular, it outlines what needs to be done and how.
 - Ideally, this project should be decomposed into a number of repos, to make it clear what the various components do and to better expose and document them for reuse.

## Notes

These files were written by Colm Bhandal, PhD student, Foundations and Methods group,
School of Computer Science and Statistics, Trinity College, Dublin, Ireland.
