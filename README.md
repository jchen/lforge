# Lforge

_Lforge_ is an implementation of Forge/Alloy syntax via a translation as a language extension of Lean 4. 

This repository is the software artifact for "Lforge: Extending Forge with an Interactive Theorem Prover", my Math-CS senior honor thesis. The paper can be found [here](https://raw.githubusercontent.com/jchen/lforge/main/paper/paper.pdf). 

## Installation

To use Lforge in your project, add the following line to your `lakefile.lean`: 
```
require Lforge from git "https://github.com/jchen/lforge.git" @ "main"
```
Then, in files that you wish to include Forge specifications, you should add
```
import Lforge
```
as the import statement. After which, you can include Forge code and syntax as usual. Hovering over definitions will show the specific generated declarations, and Lforge will prompt you if any syntax is unsupported. 
