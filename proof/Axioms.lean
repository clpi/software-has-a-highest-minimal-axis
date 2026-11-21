/-
  The dependency audit for the highest minimal axis core.
  Every theorem of the core and of the controls is printed
  with the foundational principles it depends on; the
  family gate fails if any printed principle lies outside
  the allowed set of three.
-/

import Hma
import Controls

open Hma

#print axioms filterlenmono
#print axioms filterlenstrict
#print axioms summmono
#print axioms sumstrict
#print axioms filtercongr
#print axioms subsetrefl
#print axioms subsettrans
#print axioms subsetall
#print axioms agreeoffmono
#print axioms livemono
#print axioms livemem
#print axioms engagedmono
#print axioms mumono
#print axioms lammmono
#print axioms cardle
#print axioms lamle
#print axioms filternil
#print axioms mapcongr
#print axioms mapsumzero
#print axioms cardstrict
#print axioms engagedofsufficient
#print axioms engagedlistofsufficient
#print axioms filtermemsublists
#print axioms subsetrep
#print axioms minimalexists
#print axioms highestfromminimal
#print axioms highestexists
#print axioms highestproper
#print axioms highestmax
#print axioms highestunique
#print axioms variationcomp
#print axioms variationrefl
#print axioms transid
#print axioms transcomp
#print axioms highestengaged
#print axioms degenerate
#print axioms emptyoronehighest
#print axioms mueqofliveeq
#print axioms deadremovesufficient
#print axioms deadnotminimal
#print axioms livelistsubset
#print axioms monotone
#print axioms Ctl.sublists012
#print axioms Ctl.xvalues
#print axioms Ctl.xlives
#print axioms Ctl.xaminimal
#print axioms Ctl.xcminimal
#print axioms Ctl.xahighest
#print axioms Ctl.xcdeadandminimal
#print axioms Ctl.xcnothighest
#print axioms Ctl.xdeadnotminimal
#print axioms Ctl.dvalues
#print axioms Ctl.dnoproper
#print axioms Ctl.danswer
#print axioms Ctl.dfullhighest
#print axioms Ctl.evalues
#print axioms Ctl.eonehighest
#print axioms Ctl.etwohighest
