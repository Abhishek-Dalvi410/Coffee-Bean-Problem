--------------------------------- MODULE CB ---------------------------------
EXTENDS Integers
CONSTANTS X, Y, Z
ASSUME /\ X \in 0..100
       /\ Y \in 0..100
       /\ Z \in 0..100
       /\ X+Y+Z > 0      
(*******************************************************************************************
--fair algorithm CB {
    variable r=X, g=Y, b=Z;
        {S:while (TRUE)
            {either
                {await  (r>1);
                    r:=r-2;
                 };
             or
                {await (g>1);
                    g:=g-2;
                    };
             or
                {await (b>1);
                    b:=b-2;
                    };
             or
                {await (r>0 /\ g>0);
                    r:=r-1; g:=g-1; b:=b+1
                    };
             or
                {await (g>0 /\ b>0);
                    g:=g-1; b:=b-1; r:=r+1
                    };
             or
                {await (b>0 /\ r>0);
                    b:=b-1; r:=r-1; g:=g+1
                    };
            }
        }
 }


*******************************************************************************************)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-4b438aebbd77830f73a3c8dc8ac321c0
VARIABLES r, g, b

vars == << r, g, b >>

Init == (* Global variables *)
        /\ r = X
        /\ g = Y
        /\ b = Z

Next == \/ /\ (r>1)
           /\ r' = r-2
           /\ UNCHANGED <<g, b>>
        \/ /\ (g>1)
           /\ g' = g-2
           /\ UNCHANGED <<r, b>>
        \/ /\ (b>1)
           /\ b' = b-2
           /\ UNCHANGED <<r, g>>
        \/ /\ (r>0 /\ g>0)
           /\ r' = r-1
           /\ g' = g-1
           /\ b' = b+1
        \/ /\ (g>0 /\ b>0)
           /\ g' = g-1
           /\ b' = b-1
           /\ r' = r+1
        \/ /\ (b>0 /\ r>0)
           /\ b' = b-1
           /\ r' = r-1
           /\ g' = g+1

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-641e08bc6e7c95f16dc7379efed12d2d

invariant == (r+g+b>=0)
termination == <> (r+g+b<=1 /\ r+g+b>=0)

\* nontermination1 and nontermination0 are for checking the ending at all even constants or all odd constants
nontermination1 == <> (r+g+b=1)
nontermination0 == <> (r+g+b=0)
=============================================================================
Invariant is P={r+g+b>=0} because:-
    invariant == (r+g+b>=0); this invaraint doesn't throw an error while model checking
    stable(P)
    P/\G=>P(x,e)
    
    (r+g+b>=0) /\ (r>1) => r-2+g+b>=0
    (r+g+b>1) => r+g+b>=2 (This holds)-1st
    /\
    (r+g+b>=0) /\ (g>1) => r+g-2+b>=0 (This holds;similar to the 1st one)-2nd
    /\
    (r+g+b>=0) /\ (b>1) => r+g+b-2>=0 (This holds;similar to the 1st one)-3rd
    /\
    (r+g+b>=0) /\ (r>0/\g>0) => r-1+g-1+b+1>=0
    (r+g+b>=0) /\ (r>0/\g>0) => r+g+b>=1
    (r+g+b>=2) => r+g+b>=1 (This holds)-4th
    /\
    (r+g+b>=0) /\ (g>0/\b>0) => r+1+g-1+b-1>=0 (This holds; similar to 4th one)-5th
    /\
    (r+g+b>=0) /\ (r>0/\b>0) => r-1+g+1+b-1>=0 (This holds; similar to 4th one)-6th
    
    Also from running the models using --fair algorithm;
    i.e the algorithm cannot halt if it has at least one enabled action:-
            if X,Y and Z(declared constants), are all even(includes 0) or all odd:
                model terminates at r+g+b=0 thus comes under r+g+b>=0
            else:
                model terminates at r+g+b=1 thus comes under r+g+b>0
 
Fixed Point is 0<=r+g+b<=1 because:-
    (r>1)' /\ (g>1)' /\ (b>1)' /\ (r>0 /\ g>0)' /\ (g>0 /\ b>0)' /\ (r>0 /\ b>0)'
    (r<=1) /\ (g<=1) /\ (b<=1) /\ (r=0 \/ g=0) /\ (g=0 \/ b=0) /\ (r=0 \/ b=0)
    r+g+b<=1
    invaraint is given by r+g+b>=0
    Thus fixed point is 0<=r+g+b<=1
    
Progress:-
    termination == <> (r+g+b<=1 /\ r+g+b>=0); this property doesn't throw an error while model checking
    Taking r+g+b=M; M is bounded below by Zero
    To show this is a valid metric function; prove M doesn't increase by any action
        (r>1) -> r:=r-1 (r decreases hence M decreases)
        (g>1) -> g:=g-1 (g decreases hence M decreases)
        (b>1) -> b:=b-1 (b decreases hence M decreases)
        (r>0/\g>0) -> r:=r-1; g:=g-1; b:=b+1 (net effect is such that M decreases by 1)
        (g>0/\b>0) -> g:=g-1; b:=b-1; r:=r+1 (net effect is such that M decreases by 1)
        (r>0/\b>0) -> r:=r-1; b:=b-1; g:=g+1 (net effect is such that M decreases by 1)
        metric function cannot go below 0
        M eventually reaches 1 or 0, so this program terminates
        
        
\* Modification History
\* Last modified Sun Oct 18 19:05:35 EDT 2020 by admin
\* Created Sat Oct 17 01:17:14 EDT 2020 by admin
