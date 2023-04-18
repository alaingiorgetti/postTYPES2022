# Pragmatic isomorphism proofs between Coq representations

Authors: Catherine Dubois, Nicolas Magaud and Alain Giorgetti

This repository distributes a framework for dealing with different data representations, with partial automation in proving that these different representations are isomorphic. The representations and the corresponding transformations are implemented in Coq. In addition, the Coq QuickChick plugin is used to implement random generators for the different representations. The methodology, presented in [DMG23], is illustrated with its application to data related to families of lambda terms.

[DMG23] C. Dubois, N. Magaud, and A. Giorgetti. Pragmatic isomorphism proofs
        between Coq representations: application to lambda-term families.
        Accepted for publication. 2023.

## Compatibility

The code is known to work with Coq 8.10.2 and QuickChick 1.2.1.

## Running the code

[Coq](https://coq.inria.fr) and the Coq plugin [QuickChick](https://github.com/QuickChick/QuickChick) are assumed to be installed.

Run the case study as follows:

         cd src
         make

## Project home

[https://github.com/alaingiorgetti/postTYPES2022](https://github.com/alaingiorgetti/postTYPES2022)

## Copyright

This program is distributed under the GNU GPL 3. See the enclosed LICENSE file.

