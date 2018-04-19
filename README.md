# sage-gammoid-dump
extension package for sage that consists of various code useful for gammoid-related computations

# Installation

```
sage -p gx-0.1.spkg
```

(You might have to install some python packages via `sage -pip ....` in order to compile.)

# Usage

```
import gx

gx.getAlphaSystem(gx.MK4())

help(gx)
```

# Package Contents

gx - Gammoid Tools for SAGE.

## DESCRIPTION

This package is experimental. Use at your own risk and ALWAYS DOUBLE CHECK ANY RESULTS!

## FUNCTIONS

###AcyclicGammoidLinearRepresentation(D, S=None, E=None, matrix=False, M=False, fancy=False, mat_dict=False)

    D __ *ACYCLIC* Digraph
    S __ sinks
    E __ matroid elements

    matrix __ if true return matrix instead of dictionary
    M __ if true, return linear matroid for the matrix
    fancy __ if true, use 'speaking edge' variable names
    mat_dict __ if true, return a matrix and two dictionaries giving row and column
                assignments

    returns a dictionary of vectors representing the gammoid represented by the
    _acyclic_ digraph D

###BiApexMatroid(k)

    k __ Parameter k, k>= 2

    returns the bi-apex matroid B(k)

###CircuitBasisMatroid(circuits, groundset=None)

    circuits __ set of circuits of a matroid

    groundset __ optionally a groundset for the matroid,
                 most useful if there are coloops

    returns a BasisMatroid that corresponds to the circuits given

###DigraphInducedMatroid(D, T, E=None)

    D __ digraph
    T __ matroid
    E __ (optionally) vertices of the induced matroid

     returns the induced wrt. to the digraph D,
     the target matroid T,
     and the set of matroid elements E.

     If E==None, then E=V is used.

###DirectSumMatroidM,N __ matroids

    returns the direct sum of M and N

###FreeMatroid(E)
    E __ groundset

    returns the free matroid on E

###Gammoid(D, S=None, E=None)

     returns the gammoid wrt. to the digraph D,
     the set of sinks S,
     and the set of matroid elements E.

     If E==None, then E=V is used.

###LinearBasisMatroid(A)

    A __ matrix whose columns are vectors representing
          the elements of the matroid

    returns a basis matroid in column numbers that is
          represented by A

###MK(n)

    returns MK(n)

###MK4()

    returns the MK(4) matroid.

###Mbeta(a,b,c,d,e,f)


    returns the M_beta matroid for the given configuration

    (Bonin, Savitsky)

###MbetaSets(a,b,c,d,e,f)


    returns the M_beta matroid sets
    A,B,C,D,E,F for the given configuration

    (Bonin, Savitsky)

###PathDigraph(path1, path2, ...)

    creates a digraph from the paths given by the vertex lists.

###TransversalMatroid(A)

    A __ family of subsets of the groundset E


    returns a BasisMatroid where the independent sets correspond to the
            partial transversals of the family A

###UniformMatroid(E)
    E __ groundset
    r __ rank

    return the uniform matroid UallDependentFlats(M)

###allFlats(M)

    return a chain-iterator of all flats of M, with ascending rank

###allModularPairsOfFlats(M)

    returns all modular pairs of flats (i.e. pairs of flats with zero modular defect)
             of a given matroid M.

###allRoutingsBetween(D,T,E)

    D __ digraph
    T __ (gammoid) sinks
    E __ routing sources

    returns the set of routings from E to T in D;
           where a routing consists of a set of paths
           such no two paths do not have a common vertex

###alphaPosetCmp(M)

    M __ matroid

    returns a function that implements cmp for the alpha_M poset.
    (use it with care! a return value of 0 may be equal or incomparable!
     but it is nice for sorting stuff)

###alphaPosetDownsets(M)

    M __ matroid

    returns a function that gives the downsets of the alpha_M poset

###alphaPosetLeq(M)

    M __ matroid

    returns a function that compares whether l <= r with respect to
            the alpha_M poset, and then returns either True of False

###alphaPrimePosetCmp(M, C, e)

    M __ matroid
    C __ minimal elements of a modular cut of M
    e __ name of the extension element

    viaSage __ if True, use a matroid extension and alphaPosetDownset

    returns a function that gives the downsets of the alpha_N poset,
            that corresponds to the single element extenion of M by e
            that is described by the modular cut C.

###alphaPrimePosetDownsets(M, C, e)

    M __ matroid
    C __ minimal elements of a modular cut of M
    e __ name of the extension element

    viaSage __ if True, use a matroid extension and alphaPosetDownset

    returns a function that gives the downsets of the alpha_N poset,
            that corresponds to the single element extenion of M by e
            that is described by the modular cut C.

###alphaPrimePosetLeq(M, C, e)

    M __ matroid
    C __ minimal elements of a modular cut of M
    e __ name of the extension element

    viaSage __ if True, use a matroid extension and alphaPosetDownset

    returns a function that gives the downsets of the alpha_N poset,
            that corresponds to the single element extenion of M by e
            that is described by the modular cut C.

###alphaVector(M, throughMoebius=False)

    M __ matroid

    throughMoebius __ determines, whether alpha is calculated from the
                      nullity vector through the moebius-function of alpha_M,
                      or recursively

    returns the alpha vector of M



###arcBoundStrict(n,r)
    n __ number of elements in the ground set
    r __ rank

    returns the upper bound for the number of arcs needed
    to represent a *strict* gammoid with n elements of rank r

###arcMinimalGammoidStdReprB(M, T=None, vertexLimit=None, arcLimit=None)

    M __ matroid
    T __ (optional) sink set (use any base of M)

    find a standard representation with the sink set T that has a
       minimal cardinality arc set.

###augmentListbacktrackBipartiteInduction(M, N)

    M __ matroid
    N __ matroid

    returns a set D of pairs (p,q), such that X is independent in M
    if it can be matched to an independent set Y of N using arcs from D
    or None if this is not possible

###calculateAlphaOfExtension(e, C, M, alpha=None, mu=None)


        e __ name of the new element
        C __ modular cut of the new element (whole cut, not just minimal elts!)
        M __ matroid

        alpha __ alpha vector of M
        mu  __ Möbius function of the alpha_M-poset

    returns the alpha vector of M+e that corresponds to C

###calculateArrowRelation(G,M,I)

    (G,M,I) __ formal context,

        where G, M are lists of objects and attributes, resp.,
        and I is a tuple of row-tuples of I, so if
        g = G[i] and m = M[j], then
        I[i][j] == True  iff  gIm in the context.

    returns the arrow-relations of the context, where the relation is folded as is I,
        and where 0 codes no arrow,
                  1 codes g downleft-arrow m
                  2 codes g upright-arrow m
                  3 codes g upright-and-downleftarrow m

###cancelCommonFactorsInRow(A)

    A __ matrix

    divides each row by the gcd of its entries in A,

    (alters matrix)

###canonicalMatroid(M)

    M __ matroid

    returns a minor of M that has no loops, no coloops, no parallel edges
    and no coparallel edges

###canonicalMatroidLabel(M)

    M __ matroid

    returns the canonical label of the matroid M;
           which is a tuple

###canonicalizeSet(x)

    map x to its canonical labels, if it is canonical. otherwise returns None.

###catalogueAcyclicDBlackBoxes(nI, nO, internalNodes, catalogue=None)

    nI __ number of inputs
    nO __ number of outputs
    internalNodes __ number of hidden layer nodes
    catalogue __ optional, a dictionary with previously found black boxes

    returns a dictionary that maps Matrix-tuples to one corresponding DBlackBox;
          i.e. to a tuple

###cfJoin(M,A,B)

    calculates the join of two cyclic flats A,B in M

###cfMeet(M,A,B)

    calculates the meet of two cyclic flats A,B in M

###checkAlpha(M,complete=False,negativeKeys=False)


    calculate alpha values for all subsets of E(M),
    stop, if for some subset, alpha < 0;
    unless complete=True

###checkClassForInduceds(C)

    C __ list of matroids

    returns a list of matroids from C and duals of matroids from C
            which have induced elements

###checkOMAxiomC4p(C)
    C __ family of signed circuits

    returns a list of counterexamples to (C4') in C,
    that is, counterexamples to weak signed circuit elimination.
    The counterexamples are given in the form
     (C1,C2,e)   where
       __ C1, C2 are signed circuits from C,
       __ e is such that (e,i) is in C1 and (e,-i) is in C2,
         and C1(e) = -C2(e) != 0,
         and C1 != -C2,
         but for no circuit Z in C there Z(e) = 0, and for all x
          Z(x) \in {C1(x),C2(x),0}.

###classifySingleElementExtensions(M, x="-1")

    M __ matroid

    x __ name of the new element, defaults to -1

    returns a dictionary, where the values are lists representatives
            of isomorphism classes of single element extensions of M.

###closeBinaryOps(initial, bin_ops, asymmetric=False)

    returns the closure of a given initial set under a
    given set of binary operations

    initial __ initial elements
    bin_ops __ list/tuple/etc. that contains binary ops

    [optional]
    asymmetric __ set to True, if for some ops, op(x,y) != op(y,x).
                defaults to False.

###cmpRs(R1,R2, cmp=cmp)

    R1, R2 __ routings

    cmp __ comparison function for the arcs

    return a comparison between R1 and R2,
    where the routing that contains the biggest arc that the other
    routing does not possess, wins

###cmpWrtFlats(l,r, flats)

    l,r __ operands

    flats __ set/family of frozensets

    compares whether l is a subset of r, and if l is a proper subset,
            whether l in flats

###combineCols(COLS, nspaces=2,ch=" ",sep=" ")

    COLS __ an array of column arrays


    nspaces __ number of spaces between the columns
         ch __ fill spacing character
        sep __ last spacing character

    returns an array of strings where all columns from COLS have between
        collated together.


###contractSignedCircuitsTo(...)
    C __ family of signed circuits
    F __ set to contract C to

    returns C|'F, the contraction of C to F

###contractVector(V, e, G)
    V __ 1 x 2**|G| Matrix
    e __ element of G
    G __ base set of the matrix

    returns the appropriately reduced matrix
            that consists only of entries corresponding to sets that contain
            e

###cyflatFamilyFor(M, X, Z=None)

    returns the maximal proper subflats that are cyclic (!better double check code!)

###decorateAlphaMatroid(M)
    M __ matroid

    returns an AlphaMatroid(M) or M, depending whether M has been decorated
    or not.

###deltaAlphaVector(M,C)
    M __ matroid

    C __ minimal elements of a modular cuts


    returns the vector of Delta alpha_M,
            where alpha_N wrt. the extension of M corresponding to C
            restricted to the groundset of M has the property

            alpha_N|(M.groundset) = alpha_M + Delta alpha_M

###deltaJA(J, A)

    J __ modular cut
    A __ family of cyclic flats

    calculate \delta_\Jcal (\Acal) as in my wrong theorem on presistent violations.

###deltaRestrictions(M,verbose=False)

    find lower bounds on the delta values of antichains of cyclic flats.

###dependentNonTrivialModularPairsOfFlats(M)

    M __ matroid

    returns a generator for all modular pairs of flats that have at least one dependent
        component, and that are incomparable with respect to subset-order.

###dereprCanonicalSet(x)

    turns a canonical representation back into a canonical label-set

###downsetWrtFlats(r,flats)

    r __ operand

    flats __ set/family of frozensets

    returns the subsets l of r, for which l <=(flats) r holds.

###encodeViolationModularCuts(M)

    M __ matroid

    returns a digraph that encodes how the modular cuts interact with
        the violations of M

###encodeViolationsDigraph(V)

    V __ violations dictionary

###extensionFlats(M, C, e, viaSage=False)

    M __ matroid
    C __ minimal elements of a modular cut of M
    e __ name of the extension element

    viaSage __ if True, then use a matroid extension combined with allFlats;
                otherwise, calculate directly

    returns the family of flats of M extended by e corresponding to the cut C

###filterPairsByCut(Pairs, A, B)

    returns pairs where one component is a subset of A and the other component is a subset of B

###filterPairsByPrincipalCuts(Pairs, Principals)

    returns all pairs such that all components are below at least one element of the principals

###findGammoidConstruction(M, vertexLimit=None)

    M __ matroid

    vertexLimit __ (optionally) max. number of elements of the strict gammoid

    returns either a strict gammoid N and a construction history how
            M may be constructed from N,
           or False

###findMatroidIsomorphism(...)
    returns either a map proving that M is isomorphic to N,
    or None otherwise.

###findPossibleRightmostBaseMap(M)

    M __ matroid

    returns a rightmost base map; if there is one;
    otherwise returns False

###findSetSystemInjection(SRC, TRG, partial=None, all=False, induced=False)

    find an injection of the sets in SRC into TRG, such that there is also an injection of elements

    partial is a partial set system injection that should be extended.

###findSetSystemIsomorphism = findSetSystemIsomorphismIncidenceStructure

returns either None or a map phi, such that for all
    x in A, phi[x] in B; i.e. an isomorphism of Incidence Structures

###findSetSystemIsomorphismDigraph

returns either None or a map phi, such that for all
    x in A, phi[x] in B; i.e. an isomorphism of Incidence Structures;
    uses Digraphs

###findSetSystemIsomorphismIncidenceStructure
returns either None or a map phi, such that for all
    x in A, phi[x] in B; i.e. an isomorphism of Incidence Structures

###findSetSystemIsomorphismRecursive
returns either None or a map phi, such that for all
    x in A, phi[x] in B; i.e. an isomorphism of Incidence Structures;
    uses recursion on partial phi's

###findViolations(M)

    M __ matroid


    returns a dictionary D,
            where each key is a violation X in V(M)

###formatRouting(R, headline=None, cmp=cmp)

    R __ routing


    cmp __ comparison function for the natural ordering of sources and sinks
           (used to determine the sign of the permutation)

    returns an array of strings that displays the routing

###freeSlackVector(Z)

    returns a 'sum term dict' that corresponds to the slack of a given family, where the rank function is free (a variable)

###gammoidsDb()

    return a handle to the gammoids database

###gdbCreateFamilyTable(prefix, suffix="_families",db=None)

    create a table that can store families of subsets

###gdbCreateParameterSetTable(params, prefix, suffix="_params", prefix2=None, suffix2="_status", db= None)

    create a table that can hold the representations of parameter sets,
    and fill it

###gdbCreateSubsetTable(prefix, suffix="_subsets",db=None)

    creates a table that can store subsets.

###gdbFillFamilyTable(prefix, families, prefix2= None, suffix="_families", suffix2="_subsets",db=None)

    fills a subset-family table with the given families

###gdbFillFamilyTableByIds(prefix, families, prefix2= None, suffix="_families", suffix2="_subsets",db=None)

    here the families are not actual sets but ids of subsets.

    fills a subset-family table with the given families

###gdbFillSubsetTable(prefix, family, suffix="_subsets",db=None)

    fills a subset table with a given family of subsets; (id = auto)

###gdbFillSubsetTableWithId(prefix, family, suffix="_subsets",db=None)

    fills a subset table with a given family of subsets; (id = 1,2,...)

###gdbGetFamilyWithId(id_, prefix, prefix2=None, suffix="_families", suffix2="_subsets",db=None)

    return the subset family with a given id from the family table

###gdbGetMaxId(table,db=None)

    returns the maximal `id` value of a table, of 0 if there is no such id.
    Useful for iterating over all `id`s.
    Remember that the first `id` is supposed to be 1 (!)

###gdbGetNextFreeId(table,db=None)

    get the next free id number to be used in the given table

###gdbGetSubsetId(subset, prefix, suffix="_subsets",db=None)

    return the subsets id from the subset table

###gdbGetSubsetWithId(prefix, family, suffix="_subsets",db=None)

    return the subset with a given id from the subset table

###gdbSQL(sql, args=None, commit=True, results=True, db=None, newDb=gammoidsDb)

    executes sql command on db (or newDb()),
    gives either results or a cursor object; some automatic retries

###gdbSQLbulk(sqls, argss=None, commit=True,results=True,db=None)


    executes sql commands on db or gammoidsDb(),
    gives either results or a cursor object of last command

###gdbTableExists(table,db=None)

    check whether there is a given table in the database

###getAllColines(M)

    returns all colines of M (i.e. flats with rank rk(M)-2)

###getAllCopoints(M)

    returns al copoints of M

###getAllFlatsWithElement
    returns all flats of M that contain the element e

###getAllInducedAndDuallyInducedElements(M)

    M __ matroid

    returns a pair of lists, where the first component consists of
    the induced elements of M, and the second component consists of the
    induced elemens of M.dual()

###getAllModularCuts(M)

    M __ matroid

    returns all modular cuts of M, except the empty modular cut.
    (SAGE does not allow an extension with a coloop through M.extension !!)

###getAlpha(M,X)

    M __ matroid
    X __ subset of the groundset

    returns alpha_M(X), the value of Mason's alpha function for the set X

###getAlphaSystem(M)
    calculate the alpha-transversal system of M

###getAlphaTMatroid(M)

    M __ matroid

    returns the transversal matroid of all partial transversals of \mathcal{A}_M;
    where we rather ignore negative alpha values.

###getArcSet(R)

    R __ list of paths

    returns the combined arc set of the paths in R

###getBurmeisterString(G,M,I, name="unnamed")


    (G,M,I) __ formal context,

        where G, M are lists of objects and attributes, resp.,
        and I is a tuple of row-tuples of I, so if
        g = G[i] and m = M[j], then
        I[i][j] == True  iff  gIm in the context.

    name __ optional name of the context

    returns the corresponding Burmeister context file.

###getCanonicalElement(nbr)
    returns the label for the nbr-th canonical element

###getCanonicalElementList(reqLen=None)

    returns a list of canonical names for elements; of requested length.

###getCanonicalId(x)

    returns the nbr of the canonical element that is labeled by x

###getCatIdgetChiSign(X, finschi_vector="+++++++++++++-++--++", orderedE=None)

    X __ subset of {1,2,...,n} of rank cardinality for which the sign is desired

    returns the sign of chi(X) of the matroid given by a vector from Lukas Finschi's O.M. db.

###getCoflowLattice(C)

    C __ family of signed subsets of C


    returns a pair
        (E, L)
            where E is a list mapping the column indexes to their elements wrt. C
            and L is an IntegerLattice that corresponds to the coflow lattice of C

###getCyclicFlatAlphas(M)

    M __ matroid


    returns a dictionary that maps each cyclic flat of M
           to its Mason's alpha statistic.

###getCyclicFlatBetas(M)

    M __ matroid


    returns a dictionary that maps each cyclic flat of M
           to its transversal matroid beta statistic.

           A transversal system representing M consists of
           the complements of the keys of beta with
           the multiplicity given by the value of that key.

###getCyclicFlats(M)

    returns all cyclic flats of the matroid M

###getCyclicSets(M)

    returns all cyclic sets of the matroid M,
    which is the union semilattice of all circuits of M

###getDBlackBox(D,X,Y)

    D __ digraph
    X __ input vertices
    Y __ output vertices

    returns a matrix that codes lambda_(X,D,Y)

###getDbCursor(db)


       return a new cursor of the database db; automatic retries.

    REMEMBER: INSERTING VIA CURSOR NEEDS TO BE COMMITED VIA THE DATABASE OBJECT

###getDiGraphVariableToArcMap(D, S=[])

     D __ *ACYCLIC* Digraph

    (S __ optional: sink set for gammoid)

     returns a dictionary which maps symbolic indefinites to arcs of D.

###getFileContents(name)

    returns the contents of the file

###getFinschiIndexAndSign(X ,orderedE=None)

    X __ subset of {1,2,...,N} of correct cardinality,
         for which the corresponding index of the Finschi chirotope string
         is desired

    returns (I,s) where
        I is the column index for looking up a particular tuple of elements of E,
        and s is the permutation sign (+1) or (-1).

###getFixedPattern(M)

    M __ matroid.

    returns a pattern that corresponds to Finschi-DB orientations of M

###getFlatBases(M,F)
    M __ matroid
    F __ flats

    returns all bases of the flat F

###getFlatDifference(M1, M2, dependentOnly=False)

    M1, M2 __ matroids

    dependentOnly __ if True, only return dependent flats.

    returns the flats of M1, that are not flats of M2

###getFlatLatticeStandardContext(M)

    M __ matroid

    returns (G,M,I) of the standard context of the lattice of flats of
            the matroid M. The set G corresponds to rank-1 flats (atoms),
            and the set M corresponds to rank-(r-1) flats (hyperplanes, coatoms),
            whereas I corresponds to the subset relation between G and M.

        where G, M are lists of objects and attributes, resp.,
        and I is a tuple of row-tuples of I, so if
        g = G[i] and m = M[j], then
        I[i][j] == True  iff  gIm in the context.

###getGrepPattern(M)

    M __ matroid

    returns a string that can be used to grep orientations of M from
    L. Finschi's dbomview output

###getIndetMatrix
    n __ elements (= number of rows)
    r __ rank (= number of columns)

    returns a matrix filled with variables that resembles the shape of
            a matrix representing a given matroid on n elements and rank r

###getIntersectionSemilattice(atoms)

    returns the obIntersection - semilattice of the atoms.

###getLeadingMonomial(term,order)

    term  __ some term containing variables
    order __ tuple/list that prioritizes some variables over others.

    returns the leading monomial of term wrt. order.

###getMBlackBox(M, B=None)

    M __ matroid

    B __ base of M (optional; otherwise use M.bases()[0])

###getMatroidAutomorphismGroup(M)

    M __ matroid

    returns the automorphism group of M

###getMaximalFamily(A)

    returns the subfamily of A that consists of the inclusion maximal sets

###getMaximalPartialTransversals(T)

    T __ family of subsets of some groundset


    returns maximal (partial) transversals for T

###getMaximalRouting(X, Rs, cmpRs=cmpRs)

    X  __ source set
    Rs __ list/set of routings

    cmpRs __ comparison function for the routings

    returns the routing starting in X that is maximal
        with respect to the arc order.
    [this uses the natural order on the arcs]

###getMinimalFamily(A)

    returns the subfamily of A that consists of the inclusion minimal sets

###getModularCutForElement(M,e)

    returns the modular filter that corresponds to extending
    M\e by e.


###getPathArcSet(p)

    p __ path (tuple or list)

    returns the set of arcs of p

###getPointsOnColine(M)

    returns all points of M, that are on a given coline

###getPulledOverModularCutForElements(M,e0,e1)

    returns the pulled-over modular cut(?-candidate?) for e1 as extension of M\e1
    to extend M\{e0,e1};
    as it is in my wrong theorem on persistent violations.

###getRightmostBase(F,D,T)

    F __ flat of the strict gammoid for (D,T),
         subset of the vertices of D
    D __ digraph
    T __ set of (gammoid) sinks

    returns the unique rightmost base of F wrt. getRightmostBaseMap(D,T, M=None)
    D __ digraph
    T __ set of (gammoid) sinks
    M __ (optional) Gammoidreturns a dictionary that maps all dependent flats to its rightmost bases

###getSetLattice(atoms)

    returns the obUnion, obIntersection - lattice of the atoms.

###getSetLatticeLineDiagram(A)

    A __ set family

    returns the lattice line diagram digraph for A

###getSignedCircuits(D,T,E, negativeArcs=[], cmp=cmp, verbose=None)

         D __ digraph
         T __ target vertices
         E __ groundset of the Gammoid

    negativeArcs __ set of arcs that are considered to have a negative weight
             cmp __ comparison function for arc and vertex orders

         verbose __ where to print verbose information

         returns M,R,C where
          M __ is the underyling Gammoid
          R __ consists of all routings from E to T in D
          C __ is a frozenset of signed subsets,
                 where each signed subset consists of a
                 pairs (c,sgn) where sgn is either +1 or -1, and c is an element
                 of the gronudset

###getSignedCocircuits(C, groundset=None)

    C __ family of signed circuits of an oriented matroid

    groundset __ optionally give groundset of oriented matroid,
                 useful for coloops

    return C*, the signed cocircuits of the oriented matroid given by C

###getSimpleSinkPaths(D, S=None, V=None)

    D __ digraph

    S __ optional, set of sinks
    V __ optional, set of start vertices

    returns all simple paths ending in sinks and starting in vertices of the gammoid

###getTrueCircuitClosures(M)

    returns all circuit closures, that are indeed dependent.

    (The CircuitClosuresMatroid class works with input like
      M=  CircuitClosuresMatroid(groundset="abc", circuit_closures={3:["abc"]})
      and even returns True on M.is_valid() )

###getUnionSemilattice(atoms)

    returns the obUnion - semilattice of the atoms.

###getVar
    returns some SR.var for nbr

###gx_version()

    returns the version of this EXPERIMENTAL library.

###hasInducedElement(M)

    M __ matroid

    returns [e] if M has at least one induced element e,
    or [] otherwise

###hasMK4Minor(M)

    test whether M has MK4() minor

###hasNonStrictRk3Minor(M)

    M __ matroid

###hasObviousNonGammoidMinor(M)

    returns true, if M or M.dual() has a rank 3 minor that is not a strict gammoid

###hasSubsetSubimageProperty
    phi __ map that maps sets to setStr

    return Test, if for X,Y with X.issubset(Y) the property
            phi[X].issubset(phi[Y]) holds. Returns a list of
            counterexample 4-tuples (X,Y,phi[X],phi[Y]);
            or an empty list if the property holds.

###inPrincipalCut(A, Principals)

    tests whether A is a superset of any of the principal sets, and therefore is in the filter generated by
    Principals

###incrementByOne(now, ends)

    now  __ (rw-array) current position
    ends __ strict upper-bounds for each now[i]

    increments the now array by one; where elements with higher index
               have lower significance.
        if for some index the upper bound is it, it is replaced by 0
        and the next more significant index is incremented by one...

    returns the lowest index that has been set to zero
            (return value might point out of the array!)

###ingletonViolation(M, sloppy= None)

    M __ matroid

    tests the violation of the Ingleton condition for singleton sets W,X,Y,Z

    sloppy __ (optionally) set a maximum cardinality for W,X,Y, and Z each.

    returns (W,X,Y,Z) if Ingleton's condition is violated for such a tuple,
    or None.

###intersectAll(X)

    X __ family of sets

    returns \bigcap X

###inverseMatroidInduction(D, T, M)

    D __ digraph
    T __ set of targets
    M __ matroid that shall be induced from T

    returns a family of minimal sets of T that have to be dependent.

###isAntiChain(x)

    check whether x is an anti-chain of sets.

###isCanonicalSet(x)

    test whether x only contains canonical labels

###isCyclicSet
    check whether the set S is cyclic in M

###isElementInduced(M, e)

    M __ matroid

    e __ element of the groundset

    tests, whether the element e is induced from M.deleteby a digraph. (Which then is a digraph on M.groundset(), such
          that the only non-sink is the element e)

###isGammoid(M, vertexLimit=None, arcLimit=None)

    M __ matroid

    vertexLimit __ max. number of vertices allowed in representation
    arcLimit    __ max. number of arcs allowed in representation

    returns either False if M is not a gammoid (with restrictions),
            or a representation triple (D,T,E)
                    D __ digraph
                    T __ target nodes
                    E __ ground set

###isIncomparable
    return true, if neither A subset B nor B subset A

###isInflated(M, X=None)

    M __ matroid
    X __ (optionally) a subset of the groundset of M,
         X=M.groundset() by default
    returns a list of elements x from X that correspond to modular cuts
            of M.delete([x]) which are principal filters of a single flat.

###isReorientation
        C, D __ families of signed subsets {(x1,sgn(x1)), (x2,sgn(x2)), ...}
            that are the signed circuits of an oriented matroid.

    returns B,X,Y
     where B
         ==True if D is a subset of a reorientation of C
             then  Y is a list of elements that have to be flipped,
             i.e. D \subseteq _\sigma C_{-X};
             X is ignored
         ==False if D is not a subset of a reorientation of C
             then X consists of elements of D that certify this property,
             Y is the last candidate of flips

###isStrictGammoid(M)

    M __ matroid

    return False if M is not a strict gammoid,
       and True if it is.

###isStrongBaseOrderable(M, E0=None)

     M __ matroid

     E0 __ optionally a subset of the groundset of M;
           such that the property of strong base-orderability is not tested
           for base pairs that do not contain at least one element of E0

    return False if there are bases B1,B2 where B1.union(B2).intersection(E0) is
    not empty, such that there is no bijection phi between B1.difference(B2)
    and B2.difference(B1) with the property that for every subset X of B1,
    B1.difference(X).union(phi[X]) is a base of M.
    (E0 is useful for single-element extensions).

###leqWrtFlats(l,r, flats)

    l,r __ operands

    flats __ set/family of frozensets

    compares whether l is a subset of r, and if l is a proper subset,
            whether l in flats;
            returns True if l <=(flats) r.

###lexicographicTuples
    E __ groundset
    r __ rank

###liftDipathCycle(D, c=None, x0=None, t0=None):

    D __ Digraph

    optional argument:
    c   __ cycle path in D
    x0  __ name of the new non-sink vertex in D
    t0  __ name of the new sink vertex in D


    returns a DiGraph that is the lifting of the cycle c, x0, t0;
            if no cycle is given and D does not contain a cycle,
            returns D itself.

###linearSubclassToModularCut
    M __ matroid
    L __ linear subclass

    returns the
        modular cut that corresponds to the linear subclass

###loadListOfFamilies(filename, name=None)


    restore a list of families from a given file,
    possibly overriding its name

###mapViaGraph
    G __ arcs of a graph
    x __ vertex

    maps the element x to the end of the first arc that starts in x

###mapViaGraphInverse
    G __ arcs of a graph
    x __ vertex

    maps the element x to the start of the first arc that ends in x

###minimalViolationsOfHallCondition(A)
    A __ dictionary: family of sets
    returns a list of all minimal violations of hall's condition for A

###modularClosureOfPrincipalCut(Pairs, Principals)

    Pairs      __ set of (some) modular pairs of a matroid
    Principals __ family of sets that generate a cut

    returns generators of a cut that contains the modular flat intersections of pairs in
            the input cut generated by Principals

###modularCutOfElement(M, e)

    M __ matroid
    e __ element of M

    returns the modular cut of M\e that restores M.

###modularDefect(M,A,B)

    return the modular defect of A and B in M, i.e.
    rk(A) + rk(B) - rk(A/\B) - rk(A\/ B)

###moebiusMatrixForAlphaPoset(M)

    M __ matroid

    returns the Moebius-function of the alpha_M poset.

###newPrincipalElements(Pairs, Principals)

    Pairs      __ set of (some) modular pairs of a matroid
    Principals __ family of sets that generate a cut

    returns intersection flats of modular pairs that must be in Principals if it is a modular cut

###niceCmp
    compares (a,b) first by their len() property,
    then by their inner cmp property

###niceFreeVector(d)

    nice string repr. for a free sum term dictionary

###niceStr(F)

    F __ set family

    nice printing set families

###nonEmptyAntiChains(s)

    s __ family of sets

    return subsets of the family s, which are anti-chains

###nonModularPairs(M)

    returns a list of non-modular pairs of flats of the matroid M

###nonTrivialCutGenerators(M)

    returns all generators of non-trivial modular cuts of M

###nonTrivialModularPairsOfFlats(M)

    returns all non-trivial modular pairs of a matroid M.

###nullityVector(M)

    M __ matroid

    returns the nullity vector of M

###obIntersection
    returns L.intersection(R)

###obUnion
    returns L.union(R)

###oppositeDigraph(D)

    returns the opposite digraph of D

###outerMargin
    D __ digraph
    X __ set of vertices

    returns the outer-margin of X, i.e.
        the vertices that can be reached from vertices in X,
        but that are not contained in X.

###permutateVector(a, G0, phi)

    rearranges an alpha vector with respect to the new names given by ph

###pivot(A, column, row=None, unity=True, Z=False, simplify=False)

    pivot on column, row in A;

    optionally making the pivot element 1.

    Z __ pivot in the ring of integers using lcm


    simplify __ if true, call simplify() or simplify_full() on
                each rows value, if available


    works on/returns a copy of A

###pivotBase(A,B, unity=True)

    A __ matrix
    B __ set of base column indices

    unity __ if False, do not make pivoted elements 1
    Z __ if True, use Gauss-Jordan-Variant without division
                  (with all its problems)

    check __ if true, just check whether B can be pivoted
             into a base; returns True or False

    simplify __ if true, call simplify() or simplify_full() on
                each rows value, if available

    pivots in the base given by the column set B;
    i.e. such that A[:,B] is a permutation matrix.

    works/returns on a copy of A

###pivotColOps(A, row, column=None, unity=False, Z=True, simplify=False)

    pivot on row, column in A;

    using COLUMN operations

    optionally making the pivot element 1.

    Z __ pivot in the ring of integers using lcm


    simplify __ if true, call simplify() or simplify_full() on
                each rows value, if available


    works on/returns a copy of A

###pivotDigraph(D, e, b)

    'pivots' D such that the sink b 'gives' its sink
    property to its in-neighbor e, which in turn
    becomes a sink of D then.
    (See fundamental theorem/matroid induction [Mason])

    works on/returns a copy of D

###pivotsDigraph(D, p1, p2, ..., verify=True)

    'pivots' D along p1, p2, ....

    optionally verifies, whether the pivot
    operation is admissible.

    works on/returns a copy of D

###positivityOfColines(M)

    returns the difference of the number of simple copoints
    vs the number of non-simple(fat) copoints as dictionary per coline

###powergroundset(M)

    M __ matroid

    returns powerset(sorted(M.groundset()))

###powerset(s)

    return a chain-iterator for the powerset of s

###powersetEvenMinusO(s)

    return a chainsiterator for the powerset of s, excluding the empty set
                                                and every uneven-cardinality subset

###powersetMinusO(s)

    return a chain-iterator for the powerset of s, excluding the empty set

###powersetMinusOI(s)

    return a chain-iterator for the powerset of s, excluding the empty set and s

###powersetOdd(s)

    return a chain-iterator for the powerset of s, excluding any even cardinality subset

###powersetSubsetIndex(S, X)

    S __ subset of X
    X __ universe (list or implicitly sorted)

    returns the iteration index where the subset S occurs in the powerset
    iterator

###printCols(COLS)

    COLS __ columns

    quick print the columns to the screen

###printETA(what, current, total=None, granularity=1000)


    print an ETA info.

    what        __ text message
    current     __ current iteration number
    total       __ total number of iterations
    granularity __ estimation window count

###printMasonAlpha(M)
    print the alpha system

###printSignedCircuitsLatexprnF(X)

    X __ list of sets

    prints the contents of X sorted by their setStr representation

###reduceDoubleFoundedContext(G, M, I)

    (G,M,I) __ formal context,

        where G, M are lists of objects and attributes, resp.,
        and I is a tuple of row-tuples of I, so if
        g = G[i] and m = M[j], then
        I[i][j] == True  iff  gIm in the context.

    returns the reduced context (G',M',I') consisting only of
            irreducible objects and attributes, and their respective
            relations

###relabelSignedSets(C,sigma)

    C __ family of signed subsets
    sigma __ relabelling permutation, i.e.
            we call sigma(x)

    returns C, where every subset is relabelled by sigma

###relaxHyperplane(M, H)

    M __ matroid
    H __ circuit hyperplane

    returns the relaxed matroid

###reprCanonicalSet(x)

    returns a number that represents a given canonical set in binary

###resetETA()

    resets the currect ETA estimate timer.

###restrictMatrix(M, G0, G)

        M __ 2**|G| x 2**|G| Matrix
        G0 __ subset of G
        G __ base set of the matrix

        returns the appropriately reduced matrix

###restrictSignedCircuitsTo
    C __ family of signed circuits
    F __ set to contract C to

    returns C|F, the restriction of C to F

###restrictVector(V, G0, G)

    V __ 1 x 2**|G| Matrix
    G0 __ subset of G
    G __ base set of the matrix

    returns the appropriately reduced matrix

###reverseLexicographicTuples
    E __ groundset
    r __ rank

###saveBurmeisterContext(G,M,I, filename)


    (G,M,I) __ formal context,

        where G, M are lists of objects and attributes, resp.,
        and I is a tuple of row-tuples of I, so if
        g = G[i] and m = M[j], then
        I[i][j] == True  iff  gIm in the context.

    filename __ path where context is stored,
            make it end with ".cxt" in order to open it with ConExp...

###searchForAcyclicDBlackBox(rho, internalNodes, searchAll=False)

    rho __ black box
    internalNodes __ number of internal nodes
    searchAll __ if True, return a list of all acyclic digraphs that
                 have the desired black box

    returns an acyclic digraph that has the black box rho;
            or None if exhaustive search failed.

###setFamilize(F)

    turns F into a set family with appropriate frozenset types

###setStr(X)

    X __ set

    nice printing sets

###setSystemDigraph(A, X=None)

    create a set system digraph for the family A;
    where X is the universe of the set system,
    X is set to  uniteAll(A)  if X is None (default)

    returns pair (Digraph, vertex mapping)

###sgnR(R)

    R __ routing

    cmp __ comparison function for the natural ordering of sources and sinks


    returns the sign of R with respect to the builtin ordering in python

###signedSubsetOrthogonal
    C,D __ signed subsets

    returns true, if C and D are orthogonal.

###signedSubsetsToIntegerLattice(C)

    C __ set of signed subsets

    returns I,S
            where
            I __ corresponding integer lattice
            S __ support order
            L __ list of all generators (redundant)

###simplifyMatrix(A)

    A  __ matrix

    simplifies all entries of the given matrix,
    (alters matrix)

###slack(rk,Z,verbose= False)

    rk __ rank function or Matroid object

    Z  __ family of cyclic flats

    calculates the slack of Z wrt. to a rank function (or a matroid)

###sniceStr(X,sep=",")
           X __ family of signed Subsets

           sep __ separator between each signed subset

           returns a nicely formatted string

###sortMap(d)

    d __ dictionary

    returns a dictionary where all key-tuples are sorted

###ssetStr(X)

    X __ a signed set, i.e. S consists of tuples
        (s,sgn) where sgn is either 1 or -1

    returns a nice string representing the signed set

###subsetVector
    A, B __ vectors whose elements evaluate to true/false

    checks whether A is a subset of B.

###testCombinatorialOrientation(D,T,E, cmp=cmp, maxN=8200)

        D __ digraph
        T __ target vertices
        E __ groundset of the Gammoid

        cmp  __ comparison function for arc and vertex orders
        maxN __ number of test cases that triggers random testing


        tests random combinatorial orientations of D,T,E

    returns error, C,negativeArcs

###testEliminationAxiom(C)

    C __ family of circuits

    returns violations of the elimination axiom

###to2dimTuple(M)

    M __ matrix (or other kind of 2-dim array)

    returns a tuple of tuples of the contents of M

###toSignedSubset(s)

    s __ comma separated element list

    returns a signed subset dictionary for s

###transposeTupleTuple(I)

    I __ tuple of tuples.

    returns a tuple of tuples, where the i-th tuple
        corresponds to the i-th entries of the tuples of I

###uniteAll(X)

    X __ family of sets

    returns \bigcup X

###unniceStr(s)

    turn back s into F with
    s = niceStr(F)

###unpermutateMatrix(a, G0, phi)

    rearranges an mu matrix with respect to the old names

###unpermutateVector(a, G1, phi)

    rearranges an alpha vector with respect to the old names

###unsetStr(s)

    turn back s into X with
    s = setStr(X)

###upperAndLowerFringes(A, X, Y)


    find the elements of the set family A, that are just below X
    and that are just above Y, at the same time.
    returns a tuple, (lower-X fringe, upper-Y fringe)

###vertexBound
###vertexBound2

###violationModularCuts(M)

    M __ matroid

    returns a violation-modular-cut dictionary

###violations(M,a=None,x=None)

    M __ matroid

    a __ (optional) alpha value dictionary
    x __ (optional) must be given if alpha is given, set of keys where a[z] < 0 (any flats)

    returns all families of cyclic flats that are violating the strict gammoid inequalities.
    (by finding the representations for the negative alpha keys)
        (well, better check the code again!)

###writeListOfFamilies(name, filename, lst=None)


    writes a list of families to a given file

###zetaMatrixForAlphaPoset(M)

    M __ matroid

    returns the zeta matrix of the alpha_M poset.
