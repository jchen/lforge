# Lforge

_Lforge_ is an implementation of Forge/Alloy syntax via a translation as a language extension of Lean 4. This repository is the software artifact for "Title TBD", my Math-CS senior honor thesis. 

## Installation

To use Lforge in your project, add the following line to your `lakefile.lean`: 
```
require Lforge from git "https://github.com/jchen/lforge.git"
```
Then, in files that you wish to include Forge specifications, you should add the
```
import Lforge
```
import statement. If you are importing the generated definitions of Forge specifications from another file in your project, you do not need to reimport `Lforge`. 