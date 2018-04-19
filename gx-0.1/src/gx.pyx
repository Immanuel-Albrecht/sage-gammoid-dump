#coding:utf-8
r"""
Gammoid Tools for SAGE.

This package is experimental. Use at your own risk and ALWAYS DOUBLE CHECK ANY RESULTS!


"""
from sage.matroids.named_matroids import *
from sage.matroids.advanced import *
import itertools
import copy
import sys
import datetime
import random
import pymysql # install this via `sage -pip install pymysql`
import pymysql.cursors
from itertools import *
from copy import copy
#from sage.all import *
from sage.all import DiGraph,IncidenceStructure,lcm,gcd,Subsets,Permutation,Matrix

__old_dir = dir()[:] #copy the current dictionary, in order to not export it.

#*****************************************************************************
#       Copyright (C) 2015-2018 Immanuel Albrecht <mail@immanuel-albrecht.de>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#****************************************************************************#

def gx_version():
    """ ()

        returns the version of this EXPERIMENTAL library.
    """
    return (0,1,0,2)

#****************
#    eta
#****************



__last_etas = [(0,0,datetime.datetime.now())] # tuples: (percent done, current_count, time)

def resetETA():
    """ ()

        resets the currect ETA estimate timer."""
    global __last_etas
    __last_etas = [(0,0,datetime.datetime.now())]

def printETA(what, current, total=None, granularity=1000):
    """ (what, current, total=None, granularity=1000)


        print an ETA info.

        what        __ text message
        current     __ current iteration number
        total       __ total number of iterations
        granularity __ estimation window count"""
    if current == 1:
        resetETA()
    if total:
        prc = float(current) / float(total) * granularity
        rnd = int(prc)
        if __last_etas[-1][0] < rnd:
            __last_etas.append((rnd,current,datetime.datetime.now()))
        try:
            if len(__last_etas) > 1:
                estimate = (int(total-current) * (datetime.datetime.now() - __last_etas[-2][2])) \
                           / int(current -__last_etas[-2][1])
            else:
                estimate = (int(total-current) * (datetime.datetime.now() - __last_etas[-1][2])) \
                           / int(current -__last_etas[-1][1])
        except:
            estimate = "(no est./error)"
        prc = float(current) / float(total) * 100
        eta = ("[%.2g%% ETA= "%prc) + str(estimate) + "]"
    else:
        eta = "(no estimate)"
    print "\r", what, current, "/", total, eta,
    sys.stdout.flush()



#****************
#    util
#****************



# powerset variations
def powerset(s):
    """ (s)

        return a chain-iterator for the powerset of s """
    return chain.from_iterable(combinations(s, r) for r in xrange(len(s)+1))
def powersetMinusO(s):
    """ (s)

        return a chain-iterator for the powerset of s, excluding the empty set """
    return chain.from_iterable(combinations(s, r) for r in xrange(1,len(s)+1))
def powersetMinusOI(s):
    """ (s)

        return a chain-iterator for the powerset of s, excluding the empty set and s """
    return chain.from_iterable(combinations(s, r) for r in xrange(1,len(s)))
def powersetEvenMinusO(s):
    """ (s)

        return a chainsiterator for the powerset of s, excluding the empty set
                                                    and every uneven-cardinality subset"""
    return chain.from_iterable(combinations(s, r) for r in xrange(2,len(s)+1,2))
def powersetOdd(s):
    """ (s)

        return a chain-iterator for the powerset of s, excluding any even cardinality subset"""
    return chain.from_iterable(combinations(s, r) for r in xrange(1,len(s)+1,2))

def isAntiChain(x):
    """ (x)

        check whether x is an anti-chain of sets."""
    for a in xrange(len(x)):
        for b in xrange(a+1,len(x)):
            if x[a].issubset(x[b]) or x[b].issubset(x[a]):
                return False
    return True
def nonEmptyAntiChains(s):
    """ (s)

        s __ family of sets

        return subsets of the family s, which are anti-chains"""
    return filter(isAntiChain,powersetMinusO(s))

# matroid utils
def allFlats(M):
    """ (M)

        return a chain-iterator of all flats of M, with ascending rank """
    return chain.from_iterable(M.flats(r) for r in xrange(0,M.rank()+1))

def filterPairsByCut(Pairs, A, B):
    """ (Pairs, A, B)

        returns pairs where one component is a subset of A and the other component is a subset of B """
    if type(A) != frozenset:
        A = frozenset(A)
    if type(B) != frozenset:
        B = frozenset(B)
    return filter(lambda x, A=A,B=B:
                ((A.issubset(x[0]) and (B.issubset(x[1]))) or (B.issubset(x[1]) and A.issubset(x[0]))), Pairs)

def filterPairsByPrincipalCuts(Pairs, Principals):
    """ (Pairs, Principals)

        returns all pairs such that all components are below at least one element of the principals """
    def belowOne(X,Principals=setFamilize(Principals)):
        for P in Principals:
            if P.issubset(X):
                return True
    return filter(lambda x:
                (belowOne(x[0]) and belowOne(x[1])), Pairs)

def inPrincipalCut(A, Principals):
    """ (A, Principals)

        tests whether A is a superset of any of the principal sets, and therefore is in the filter generated by
        Principals """
    if type(A) != frozenset:
        A = frozenset(A)
    for P in Principals:
        if A.issuperset(P):
            return True
    return False

def getMinimalFamily(A):
    """ (A)

        returns the subfamily of A that consists of the inclusion minimal sets
        """
    A = setFamilize(A)
    Q = []
    for a in A:
        dominated = False
        for q in Q:
            if a.issuperset(q):
                dominated = True
                break
        if not dominated:
            Q = [q for q in Q if not a.issubset(q)] + [a]
    return Q

def getMaximalFamily(A):
    """ (A)

        returns the subfamily of A that consists of the inclusion maximal sets
        """
    A = setFamilize(A)
    Q = []
    for a in A:
        dominated = False
        for q in Q:
            if a.issubset(q):
                dominated = True
                break
        if not dominated:
            Q = [q for q in Q if not a.issuperset(q)] + [a]
    return Q

def newPrincipalElements(Pairs, Principals):
    """ (Pairs, Principals)

        Pairs      __ set of (some) modular pairs of a matroid
        Principals __ family of sets that generate a cut

        returns intersection flats of modular pairs that must be in Principals if it is a modular cut"""
    isct = set(intersectAll(x) for x in filterPairsByPrincipalCuts(Pairs,Principals))
    return [x for x in isct if not inPrincipalCut(x, Principals)]

def modularClosureOfPrincipalCut(Pairs, Principals):
    """ (Pairs, Principals)

        Pairs      __ set of (some) modular pairs of a matroid
        Principals __ family of sets that generate a cut

        returns generators of a cut that contains the modular flat intersections of pairs in
                the input cut generated by Principals"""
    J = newPrincipalElements(Pairs,Principals)
    while len(J):
        Principals = getMinimalFamily(set(J).union(Principals))
        J = newPrincipalElements(Pairs,Principals)
    return Principals


def modularDefect(M,A,B):
    """ (M,A,B)

        return the modular defect of A and B in M, i.e.
        rk(A) + rk(B) - rk(A/\\B) - rk(A\\/ B)"""
    return M.rank(A) + M.rank(B) - M.rank(intersectAll([A,B])) - M.rank(uniteAll([A,B]))

def allModularPairsOfFlats(M):
    """ (M)

        returns all modular pairs of flats (i.e. pairs of flats with zero modular defect)
                 of a given matroid M."""
    def RHS(A,B):
        return M.rank(A.union(B)) + M.rank(A.intersection(B))

    checks = []
    for r0 in xrange(0,M.rank()+1):
        for r1 in xrange(0,r0):
            checks.append(filter(lambda x,rsum=r0+r1: RHS(x[0],x[1]) == rsum, product(M.flats(r1),M.flats(r0))))
        checks.append(filter(lambda x,rsum=2*r0: RHS(x[0],x[1]) == rsum, combinations(M.flats(r0),2)))
    return chain.from_iterable(checks)

def isIncomparable(A,B):
    """ (A,B)

        return true, if neither A subset B nor B subset A"""
    return not (A.issubset(B)) and not (B.issubset(A))

def nonTrivialModularPairsOfFlats(M):
    """ (M)

        returns all non-trivial modular pairs of a matroid M. """
    def RHS(A,B):
        return M.rank(A.union(B)) + M.rank(A.intersection(B))

    checks = []
    for r0 in xrange(0,M.rank()+1):
        for r1 in xrange(0,r0):
            checks.append(filter(lambda x,rsum=r0+r1: (not x[0].issubset(x[1])) and (  RHS(x[0],x[1]) == rsum ),
                        product(M.flats(r1),M.flats(r0))))
        checks.append(filter(lambda x,rsum=2*r0: RHS(x[0],x[1]) == rsum, combinations(M.flats(r0),2)))


    return chain.from_iterable(checks)
# set utilities

def niceCmp(a,b):
    """ (a,b)

        compares (a,b) first by their len() property,
        then by their inner cmp property"""
    if len(a) < len(b):
        return int(-1)
    if len(a) > len(b):
        return int(1)
    return cmp(a,b)

def niceStr(F):
    """ (F)

        F __ set family

        nice printing set families"""
    s = []
    for X in F:
        if len(X):
            s.append("".join(map(str, sorted(X))))
        else:
            s.append("{}")
    s.sort(cmp=niceCmp)
    return "{"+",".join(s)+ "}"

def setStr(X):
    """ (X)

        X __ set

        nice printing sets"""
    s = []
    for x in sorted(X):
        s.append(str(x))
    s.sort(cmp=niceCmp)
    return "{"+",".join(s)+ "}"

def unniceStr(s):
    """ (s)

        turn back s into F with
        s = niceStr(F)"""
    s = s.strip()
    F = []
    if s.startswith("{"):
        s = s[1:]
    if s.endswith("}"):
        s = s[:-1]
    for x in s.split(','):
        x0 = x.strip()
        F.append(x0)
    return setFamilize(F)

def unsetStr(s):
    """ (s)

        turn back s into X with
        s = setStr(X)"""
    s = s.strip()
    F = []
    if s.startswith("{"):
        s = s[1:]
    if s.endswith("}"):
        s = s[:-1]
    for x in s.split(','):
        x0 = x.strip()
        F.append(x0)
    return frozenset(F)


def intersectAll(X):
    """ (X)

        X __ family of sets

        returns \\bigcap X"""
    ISCT = None
    for x in X:
        if ISCT == None:
            if type(x) == frozenset:
                ISCT = x
            else:
                ISCT = frozenset(x)
        else:
            ISCT = ISCT.intersection(x)
    return ISCT

def uniteAll(X):
    """ (X)

        X __ family of sets

        returns \\bigcup X"""
    UNION = None
    for x in X:
        if UNION == None:
            if type(x) == frozenset:
                UNION = x
            else:
                UNION = frozenset(x)
        else:
            UNION = UNION.union(x)
    return UNION

def setFamilize(F):
    """ (F)

        turns F into a set family with appropriate frozenset types"""
    A = set()
    for f in F:
        if type(f) == frozenset:
            A.add(f)
        else:
            A.add(frozenset(f))
    return A

def sortMap(d):
    """ (d)

        d __ dictionary

        returns a dictionary where all key-tuples are sorted"""
    d2 = {}
    for x in d:
        x2 = tuple(sorted(x))
        d2[x2] = d[x]
    return d2

def upperAndLowerFringes(A, X,Y):
    """ (A, X, Y)


        find the elements of the set family A, that are just below X
        and that are just above Y, at the same time.
        returns a tuple, (lower-X fringe, upper-Y fringe) """
    L = []
    U = []
    if type(X) != frozenset:
        X = frozenset(X)
    if type(Y) != frozenset:
        Y = frozenset(Y)
    F = setFamilize(A)

    for C in F:
        if X.issuperset(C):
            dominated = False
            for D in L:
                if D.issuperset(C):
                    dominated = True
                    break
            if not dominated:
                Lp = [C]
                for D in L:
                    if not C.issuperset(D):
                        Lp.append(D)
                L = Lp
        if Y.issubset(C):
            dominated = False
            for D in U:
                if D.issubset(C):
                    dominated = True
                    break
            if not dominated:
                Up = [C]
                for D in U:
                    if not C.issubset(D):
                        Up.append(D)
                U = Up
    return L,U

def getFileContents(name):
    """ (name)

        returns the contents of the file"""
    with open(name,"r") as f:
        return f.read()

def getVar(nbr):
    """ (nbr)

        returns some SR.var for nbr """
    if nbr < 0:
        return SR.var('a' + str(-nbr))
    if nbr < 23:
        return SR.var(chr(ord('a') + nbr))
    return SR.var('x' + str(nbr - 22))

def getSetLatticeLineDiagram(A):
    """ (A)

        A __ set family

        returns the lattice line diagram digraph for A
        """
    F = [(len(x), x) for x in setFamilize(A)]
    F.sort()
    I = {}
    for y in xrange(0,len(F)):
        I[setStr(F[y][1])] = [setStr(x) for x in getMaximalFamily([F[x][1] for x in xrange(y) if F[y][1].issuperset(F[x][1])])]
    return DiGraph(I)


#*******************
#     io
#*******************



def writeListOfFamilies(name, filename, lst=None):
    """ (name, filename, lst=None)


        writes a list of families to a given file """
    if lst == None:
        lst = globals()[name]
    with open(filename, "wb") as f:
        f.write(repr(name)+"\n")
        f.write(repr(len(lst))+"\n")
        for x in lst:
            f.write(repr(niceStr(x))+"\n")

def loadListOfFamilies(filename, name=None):
    """ (filename, name=None)


        restore a list of families from a given file,
        possibly overriding its name"""
    with open(filename,"rb") as f:
        orig_name = eval(f.readline())
        if name == None:
            name = orig_name
        print "Reading in",name
        l = []
        cnt = eval(f.readline())
        for i in xrange(cnt):
            s = eval(f.readline())
            l.append(unniceStr(s))
        globals()[name] = l

#**************
#   lattices
#**************

def closeBinaryOps(initial, bin_ops, asymmetric=False):
    """ (initial, bin_ops, asymmetric=False)

        returns the closure of a given initial set under a
        given set of binary operations

        initial __ initial elements
        bin_ops __ list/tuple/etc. that contains binary ops

        [optional]
        asymmetric __ set to True, if for some ops, op(x,y) != op(y,x).
                    defaults to False.
                    """
    new = set(initial)
    S = set(initial)
    while len(new):
        old = new
        new = set()
        for x in old:
            for y in S:
                for op in bin_ops:
                    z = op(x,y)
                    if not z in S:
                        new.add(z)
                    if asymmetric:
                        z = op(y,x)
                        if not z in S:
                            new.add(z)
        S = S.union(new)
    return S

def obUnion(L,R):
    """ (L,R)

        returns L.union(R)"""
    return L.union(R)

def obIntersection(L,R):
    """ (L,R)

        returns L.intersection(R) """
    return L.intersection(R)

def getSetLattice(atoms):
    """ (atoms)

        returns the obUnion, obIntersection - lattice of the atoms. """
    return closeBinaryOps([frozenset(x) for x in atoms],[obUnion,obIntersection])

def getUnionSemilattice(atoms):
    """ (atoms)

        returns the obUnion - semilattice of the atoms. """
    return closeBinaryOps([frozenset(x) for x in atoms],[obUnion])

def getIntersectionSemilattice(atoms):
    """ (atoms)

        returns the obIntersection - semilattice of the atoms. """
    return closeBinaryOps([frozenset(x) for x in atoms],[obIntersection])

#***********************
#    sql
#***********************

def gammoidsDb():
    """()

        return a handle to the gammoids database """
    while 1:
        try:
            return pymysql.connect(host="127.0.0.1",user="gammoids",password="violations",use_unicode=True,database="gammoids")
        except pymysql.err.OperationalError,x:
            print "Connect:" ,x
            print "Retrying..."

def getDbCursor(db):
    """ (db)


        return a new cursor of the database db; automatic retries.

     REMEMBER: INSERTING VIA CURSOR NEEDS TO BE COMMITED VIA THE DATABASE OBJECT

        """
    retries = 0
    while 1:
        try:
            return db.cursor()
        except Exception, e:
            retries += 1
            print "Cursor:", x
            print type(x)
            if retries >= 3:
                try:
                    db.commit()
                except x:
                    print "db.commit():",x
                try:
                    db.connect()
                except x:
                    print "db.connect():",x


def gdbSQL(sql, args=None, commit=True,results=True,db=None,newDb=gammoidsDb):
    """
        (sql, args=None, commit=True, results=True, db=None, newDb=gammoidsDb)

        executes sql command on db (or newDb()),
        gives either results or a cursor object; some automatic retries """
    retries = 0
    while 1:
        try:
            if db == None:
                db = newDb()
                close_db = True
            else:
                close_db = False
            cur = getDbCursor(db)
            rv = cur.execute(sql,args)

            if commit:
                db.commit()
            if results:
                r = cur.fetchall()
                cur.close()
                if close_db:
                    db.close()
                return r
            else:
                return cur
        except Exception, e:
            print "ERROR RUNNING gdbSQL",(sql,args,commit,results,db,newDb)
            print "Error = ",e
            print "Retry = ",retries
            retries += 1

            if retries >= 3:
                try:
                    db.commit()
                except x:
                    print "db.commit():",x
                try:
                    db.connect()
                except x:
                    print "db.connect():",x
            if retries >= 6:
                try:
                    db = newDb()
                except x:
                    print "db = newDb():",x


def gdbSQLbulk(sqls, argss=None, commit=True,results=True,db=None):
    """ (sqls, argss=None, commit=True,results=True,db=None)


        executes sql commands on db or gammoidsDb(),
        gives either results or a cursor object of last command """
    if argss is None:
        argss = [None for i in xrange(len(sqls))]
    if db == None:
        db = gammoidsDb()
        close_db = True
    else:
        close_db = False

    cur = getDbCursor(db)

    for sql,args in zip(sqls,argss):
        rv = cur.execute(sql,args)

    if commit:
        db.commit()
    if results:
        r = cur.fetchall()
        cur.close()
        if close_db:
            db.close()
        return r
    else:
        return cur

def gdbCreateSubsetTable(prefix, suffix="_subsets",db=None):
    """ (prefix, suffix="_subsets",db=None)

        creates a table that can store subsets. """
    sql = "CREATE TABLE `" + prefix + suffix+ "` (" + \
     "`id` int(11) unsigned NOT NULL AUTO_INCREMENT," + \
      "`cardinality` int(10) unsigned NOT NULL," + \
      "`elements` text, " + \
      "PRIMARY KEY (`id`)" + \
    ") ENGINE=InnoDB DEFAULT CHARSET=utf8 ;"#COLLATE=utf8_german2_ci;"
    gdbSQL(sql,db=db)

def gdbFillSubsetTable(prefix, family, suffix="_subsets",db=None):
    """ (prefix, family, suffix="_subsets",db=None)

        fills a subset table with a given family of subsets; (id = auto) """
    for X in family:
        r = setStr(X)
        sql = "INSERT INTO `"+ prefix+suffix+"`(`id`, `cardinality`, `elements`) VALUES (NULL, %s, %s)"
        gdbSQL(sql, (str(len(X)), r),db=db)


def gdbFillSubsetTableWithId(prefix, family, suffix="_subsets",db=None):
    """ (prefix, family, suffix="_subsets",db=None)

        fills a subset table with a given family of subsets; (id = 1,2,...) """
    id_ = 1
    for X in family:
        r = setStr(X)
        sql = "INSERT INTO `"+ prefix+suffix+"`(`id`, `cardinality`, `elements`) VALUES (%s, %s, %s)"
        gdbSQL(sql, (str(id_),str(len(X)), r),db=db)
        id_ += 1

def gdbGetSubsetWithId(id_, prefix, suffix="_subsets",db=None):
    """ (prefix, family, suffix="_subsets",db=None)

        return the subset with a given id from the subset table """

    sql = "SELECT `elements` FROM `"+prefix+suffix+"` WHERE `id` = "+str(id_);
    r = gdbSQL(sql,db=db)
    if len(r) < 1:
        return None
    return unsetStr(r[0][0])

def gdbGetSubsetId(subset, prefix, suffix="_subsets",db=None):
    """ (subset, prefix, suffix="_subsets",db=None)

        return the subsets id from the subset table """
    sql = "SELECT `id` FROM `"+prefix+suffix+'` WHERE `elements` = %s'
    x = gdbSQL(sql, setStr(subset),db=db)
    if len(x) < 1:
        return 0
    if x[0][0] is None:
        return 0
    return x[0][0]

def gdbGetFamilyWithId(id_, prefix, prefix2=None, suffix="_families", suffix2="_subsets",db=None):
    """ (id_, prefix, prefix2=None, suffix="_families", suffix2="_subsets",db=None)

        return the subset family with a given id from the family table """
    if prefix2 is None:
        prefix2 = prefix
    sql = "SELECT `subset` FROM `"+prefix+suffix+"` WHERE `id` = "+str(id_);
    r = gdbSQL(sql,db=db)
    ids = [x[0] for x in r]
    return [gdbGetSubsetWithId(x,prefix2,suffix2,db=db) for x in ids]


def gdbCreateFamilyTable(prefix, suffix="_families",db=None):
    """ (prefix, suffix="_families",db=None)

        create a table that can store families of subsets """
    sql = "CREATE TABLE `" + prefix + suffix+ "` (" + \
     "`id` int(11) unsigned NOT NULL," + \
     "`subset` int(11) unsigned NOT NULL" + \
    ") ENGINE=InnoDB DEFAULT CHARSET=utf8 ;"#COLLATE=utf8_german2_ci;"
    gdbSQL(sql,db=db)

def gdbFillFamilyTable(prefix, families, prefix2= None, suffix="_families", suffix2="_subsets",db=None):
    """ (prefix, families, prefix2= None, suffix="_families", suffix2="_subsets",db=None)

        fills a subset-family table with the given families """
    if prefix2 is None:
        prefix2 = prefix
    Fid = gdbGetNextFreeId(prefix+suffix,db=db)
    for xF in families:
        F = setFamilize(xF)
        ids = []
        for X in F:
            id_ = gdbGetSubsetId(X, prefix2, suffix2,db=db)
            if id_ > 0:
                ids.append(id_)
            else:
                raise Exception("Subset "+setStr(X)+" not in subset database! Cannot add "+niceStr(F)+"!")
        gdbSQLbulk(["INSERT INTO `"+prefix+suffix+"` VALUES (" + str(Fid) + ", "+ str(i) +")" for i in ids],db=db)
        Fid += 1

def gdbFillFamilyTableByIds(prefix, families, suffix="_families",db=None):
    """ (prefix, families, prefix2= None, suffix="_families", suffix2="_subsets",db=None)

        here the families are not actual sets but ids of subsets.

        fills a subset-family table with the given families """
    Fid = gdbGetNextFreeId(prefix+suffix,db=db)
    for ids in families:
        gdbSQLbulk(["INSERT INTO `"+prefix+suffix+"` VALUES (" + str(Fid) + ", "+ str(i) +")" for i in ids],db=db)
        Fid += 1


def gdbGetMaxId(table,db=None):
    """ (table,db=None)

        returns the maximal `id` value of a table, of 0 if there is no such id.
        Useful for iterating over all `id`s.
        Remember that the first `id` is supposed to be 1 (!)
        """
    sql = "SELECT MAX(`id`) FROM `"+table+"`"
    x = gdbSQL(sql,db=db)
    if len(x) < 1:
        return 0
    if x[0][0] is None:
        return 0
    return x[0][0]

def gdbTableExists(table,db=None):
    """ (table,db=None)

        check whether there is a given table in the database """
    sql = "SELECT * FROM INFORMATION_SCHEMA.TABLES WHERE TABLE_NAME = %s"
    x = gdbSQL(sql,(table,),db=db)
    return len(x) > 0


def gdbGetNextFreeId(table,db=None):
    """ (table,db=None)

        get the next free id number to be used in the given table"""
    sql = "SELECT MAX(`id`) FROM `"+table+"`"
    x = gdbSQL(sql,db=db)
    if len(x) < 1:
        return 1
    if x[0][0] is None:
        return 1
    return x[0][0] + 1


def gdbCreateParameterSetTable(params, prefix, suffix="_params", prefix2=None, suffix2="_status", db= None):
    """ (params, prefix, suffix="_params", prefix2=None, suffix2="_status", db= None)

        create a table that can hold the representations of parameter sets,
        and fill it"""
    if prefix2 is None:
        prefix2 = prefix
    sql = "CREATE TABLE `" + prefix + suffix+ "` (" + \
      "`parameter` text " + \
    ") ENGINE=InnoDB DEFAULT CHARSET=utf8 ;"#COLLATE=utf8_german2_ci;"
    gdbSQL(sql,db=db)
    for X in params:
        r = repr(X)
        sql = "INSERT INTO `"+ prefix+suffix+"` (`parameter`) VALUES (%s)"
        gdbSQL(sql, (r,), db=db)
    sql = "CREATE TABLE `" + prefix2 + suffix2+ "` (" + \
     "`id` int(11) unsigned NOT NULL AUTO_INCREMENT," + \
      "`parameter` text, " + \
      "`status` text, " + \
      "`agent` text, " + \
      "`ts` TIMESTAMP DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP, "+ \
      "`dt` DATETIME DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,  "+ \
      "PRIMARY KEY (`id`)" + \
    ") ENGINE=InnoDB DEFAULT CHARSET=utf8 ;"#COLLATE=utf8_german2_ci;"
    gdbSQL(sql,db=db)

#****************
# cyflats
#****************


def getCyclicSets(M):
    """ (M)

        returns all cyclic sets of the matroid M,
        which is the union semilattice of all circuits of M """
    return getUnionSemilattice(frozenset([frozenset()]).union(M.circuits()))

def isCyclicSet(M,S):
    """ (M,S)

        check whether the set S is cyclic in M """
    if type(S) != frozenset:
        S = frozenset(S)
    r = M.rank(S)
    for x in S:
        if M.rank(S.difference([x])) != r:
            return False
    return True

def cfJoin(M,A,B):
    """ (M,A,B)

        calculates the join of two cyclic flats A,B in M """
    if type(A) != frozenset:
        A = frozenset(A)
    return M.closure(A.union(B))

def cfMeet(M,A,B):
    """ (M,A,B)

        calculates the meet of two cyclic flats A,B in M """
    if type(A) != frozenset:
        A = frozenset(A)
    X = A.intersection(B)
    X0 = set()
    r = M.rank(X)
    for x in X:
        if M.rank(X.difference([x])) == r:
            X0.add(x)
    return frozenset(X0)

def getTrueCircuitClosures(M):
    """ (M)

        returns all circuit closures, that are indeed dependent.

        (The CircuitClosuresMatroid class works with input like
          M=  CircuitClosuresMatroid(groundset="abc", circuit_closures={3:["abc"]})
          and even returns True on M.is_valid() )
    """
    return filter(lambda x,M=M: M.is_dependent(x),
            itertools.chain.from_iterable(M.circuit_closures().values()))

def getCyclicFlats(M):
    """ (M)

        returns all cyclic flats of the matroid M """
    return closeBinaryOps([M.closure([])]+list(getTrueCircuitClosures(M)),[lambda x,y,M=M:cfJoin(M,x,y)])


def getCyclicFlatAlphas(M):
    """ (M)

        M __ matroid


        returns a dictionary that maps each cyclic flat of M
               to its Mason's alpha statistic. """
    Fs = [(M.rank(F),F) for F in getCyclicFlats(M)]
    Fs.sort()
    alpha = {}
    for rk,F in Fs:
        nu = len(F) - rk
        for K0 in alpha.keys():
            if K0.issubset(F):
                nu -= alpha[K0]
        alpha[F] = nu
    return alpha


def getCyclicFlatBetas(M):
    """ (M)

        M __ matroid


        returns a dictionary that maps each cyclic flat of M
               to its transversal matroid beta statistic.

               A transversal system representing M consists of
               the complements of the keys of beta with
               the multiplicity given by the value of that key.

               """
    Fs = [(M.rank(F),F) for F in getCyclicFlats(M)]
    Fs.sort(reverse=True)
    beta = {}
    R = M.rank()
    for rk,F in Fs:
        cr = R - rk
        for K0 in beta.keys():
            if K0.issuperset(F):
                cr -= beta[K0]
        beta[F] = cr
    return beta

#*****************
# matroids
#*****************



def MK(n):
    """ (n)

        returns MK(n) """
    return sage.matroids.catalog.CompleteGraphic(n)

def MK4():
    """ ()

        returns the MK(4) matroid."""
    return CircuitClosuresMatroid(groundset=xrange(6),circuit_closures=
{2: {frozenset({1, 2, 5}),
  frozenset({3, 4, 5}),
  frozenset({0, 2, 4}),
  frozenset({0, 1, 3})},
 3: {frozenset({0, 1, 2, 3, 4, 5})}})

def hasMK4Minor(M):
    """ (M)

        test whether M has MK4() minor """
    MK4 = MK(4)
    N = len(M.groundset())
    Xn = N - 6
    for F in itertools.combinations(M.groundset(), Xn):
        Mdel = M.delete(F)
        if MK4.is_isomorphic(Mdel):
            return Mdel
        Mcon = M.contract(F)
        if MK4.is_isomorphic(Mcon):
            return Mcon
    return False

def MbetaSets(a,b,c,d,e,f):
    """ (a,b,c,d,e,f)


        returns the M_beta matroid sets
        A,B,C,D,E,F for the given configuration

        (Bonin, Savitsky) """
    k = c
    if k != a + b:
        return "Error: a+b != " + str(k)
    if k != d + e:
        return "Error: d+e != " + str(k)
    if k != f:
        return "Error: f != " + str(k)
    if k < 2:
        return "Error: k < 2"
    groundlist = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890@$#!~%&-+/\\<>"[0:4*k]
    A = groundlist[0:a]
    B = groundlist[a:a+b]
    C = groundlist[a+b:a+b+c]
    D = groundlist[a+b+c:a+b+c+d]
    E = groundlist[a+b+c+d:a+b+c+d+e]
    F = groundlist[a+b+c+d+e:a+b+c+d+e+f]
    return A,B,C,D,E,F

def Mbeta(a,b,c,d,e,f):
    """ (a,b,c,d,e,f)


        returns the M_beta matroid for the given configuration

        (Bonin, Savitsky) """
    k = c
    if k != a + b:
        return "Error: a+b != " + str(k)
    if k != d + e:
        return "Error: d+e != " + str(k)
    if k != f:
        return "Error: f != " + str(k)
    if k < 2:
        return "Error: k < 2"
    groundlist = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890@$#!~%&-+/\\<>"[0:4*k]
    A = groundlist[0:a]
    B = groundlist[a:a+b]
    C = groundlist[a+b:a+b+c]
    D = groundlist[a+b+c:a+b+c+d]
    E = groundlist[a+b+c+d:a+b+c+d+e]
    F = groundlist[a+b+c+d+e:a+b+c+d+e+f]
    Zrk= [(2*k, frozenset(groundlist)),
          (2*k-1, frozenset(A+B+D+E)),
          (k+b, frozenset(C+B+E)),
          (k+a, frozenset(C+A+D)),
          (k+e, frozenset(F+E+A)),
          (k+d, frozenset(F+D+B))]
    ccs = {}
    for r,Z in Zrk:
        if not r in ccs:
            ccs[r] = []
        ccs[r].append(Z)

    return CircuitClosuresMatroid(groundset=groundlist, circuit_closures=ccs)



def getAllFlatsWithElement(M, e):
    """ (M,e)

        returns all flats of M that contain the element e """
    partial_bases = set()
    for b in M.bases():
        if not e in b:
            continue
        b0 = [x for x in b if not x == e]
        for b1 in powerset(b0):
            partial_bases.add(tuple(b1))
    flats = set()
    for b in partial_bases:
        flats.add(M.closure( b + (e,) ))
    return flats

def getModularCutForElement(M, e):
    """ (M,e)

        returns the modular filter that corresponds to extending
        M\\e by e.

        There was an error in this routine
    """
    cut_flats = set()
    for f in getAllFlatsWithElement(M,e):
        if not e in M.closure(f.difference((e,))):
            continue
        cut_flats.add(f.difference((e,)))
    return cut_flats

def getPulledOverModularCutForElements(M,e0,e1):
    """ (M,e0,e1)

        returns the pulled-over modular cut(?-candidate?) for e1 as extension of M\\e1
        to extend M\\{e0,e1};
        as it is in my wrong theorem on persistent violations."""
    C1 = getModularCutForElement(M,e1)
    C0 = getModularCutForElement(M.delete(e1), e0)
    K = set()
    for f in C1:
        if not e0 in f:
            K.add(f) # f <= cl(f) \in C0
        else:
            fx = f.difference((e0,))
            if fx in C0:
                K.add(fx)
            #otherwise cl(fx) \in C0 <=> fx \in C0; and gets added in another loop-iteration.

    return K

def deltaJA(J,A):
    """ (J, A)

        J __ modular cut
        A __ family of cyclic flats

        calculate \delta_\Jcal (\Acal) as in my wrong theorem on presistent violations."""
    for x in A:
        if not x in J:
            return 0
    mA = intersectAll(A)
    if mA in J:
        return 0
    return 1

def pivot(A,column, row=None, unity=True, Z=False, simplify=False):
    """ (A, column, row=None, unity=True, Z=False, simplify=False)

        pivot on column, row in A;

        optionally making the pivot element 1.

        Z __ pivot in the ring of integers using lcm


        simplify __ if true, call simplify() or simplify_full() on
                    each rows value, if available


        works on/returns a copy of A
    """
    Ap = copy.copy(A)
    if row is None:
        for i in xrange(Ap.dimensions()[0]):
            if Ap[i,column] != 0:
                row = i
                break
        if row is None:
            return "Error, cannot pivot zero-column %d"%column
    if unity and not Z:
        Ap[row] /= Ap[row,column]
    for i in xrange(Ap.dimensions()[0]):
        if i == row:
            continue
        if Z:
            cm = lcm(Ap[i,column], Ap[row,column])
            if cm != 0:
                a = (cm / Ap[i,column])
                if 'simplify_rational' in dir(a): # polynomials need manual cancelling
                    a = a.simplify_rational()
                b = (cm / Ap[row,column])
                if 'simplify_rational' in dir(b):# polynomials need manual cancelling
                    b = b.simplify_rational()
                Ap[i] = a*Ap[i] - b*Ap[row]
        else:
            Ap[i] -= (Ap[i,column]/Ap[row,column])* Ap[row]
        if simplify:
            for c in xrange(Ap.dimensions()[1]):
                x = Ap[i,c]
                if 'simplify_full' in dir(x):
                    Ap[i,c] = x.simplify_full()
                elif 'simplify' in dir(x):
                    Ap[i,c] = x.simplify()
    return Ap

def pivotBase(A,B, unity=True, Z=False, check=False, simplify=True):
    """ (A,B, unity=True)

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
    """
    Ap = copy.copy(A)
    rows = set(range(A.dimensions()[0]))
    for column in B:
        row = None
        for r in rows:
            if Ap[r,column] != 0:
                row = r
                #print row, "= ",Ap[row,column]
                break
        if row is None:
            if check:
                return False
            return "Error, B is not a base!"
        rows.remove(row)
        if unity and not Z:
            Ap[row] /= Ap[row,column]
        for i in xrange(Ap.dimensions()[0]):
            if i == row:
                continue
            if Z:
                cm = lcm(Ap[i,column], Ap[row,column])
                if cm != 0:
                    a = (cm / Ap[i,column])
                    if 'simplify_rational' in dir(a): # polynomials need manual cancelling
                        a = a.simplify_rational()
                    b = (cm / Ap[row,column])
                    if 'simplify_rational' in dir(b):# polynomials need manual cancelling
                        b = b.simplify_rational()
                    Ap[i] = a*Ap[i] - b*Ap[row]
            else:
                Ap[i] -= (Ap[i,column]/Ap[row,column])* Ap[row]
            if simplify:
                for c in xrange(Ap.dimensions()[1]):
                    x = Ap[i,c]
                    if 'simplify_full' in dir(x):
                        Ap[i,c] = x.simplify_full()
                    elif 'simplify' in dir(x):
                        Ap[i,c] = x.simplify()
    if check:
            return True
    return Ap

def findMatroidIsomorphism(M,N):
    """ (M,N)

        returns either a map proving that M is isomorphic to N,
        or None otherwise."""
    IM = IncidenceStructure(M.bases())
    IN = IncidenceStructure(N.bases())
    phi = IM.is_isomorphic(IN,True)
    if phi:
        return phi
    return None

def LinearBasisMatroid(A):
    """ (A)

        A __ matrix whose columns are vectors representing
              the elements of the matroid

        returns a basis matroid in column numbers that is
              represented by A"""
    r = A.rank()
    bases = set()
    for B in combinations(range(A.dimensions()[1]),r):
        if pivotBase(A,B,Z=True,check=True):
            bases.add(B)
    return BasisMatroid(groundset=range(A.dimensions()[1]),bases=bases)

def simplifyMatrix(A):
    """ (A)

        A  __ matrix

        simplifies all entries of the given matrix,
        (alters matrix)
    """
    for r in xrange(A.dimensions()[0]):
        for c in xrange(A.dimensions()[1]):
            x = A[r,c]
            if 'simplify_full' in dir(x):
                A[r,c] = x.simplify_full()
            elif 'simplify_rational' in dir(x):
                A[r,c] = x.simplify_rational()
    return A

def cancelCommonFactorsInRow(A):
    """ (A)

        A __ matrix

        divides each row by the gcd of its entries in A,

        (alters matrix)
    """
    for r in xrange(A.dimensions()[0]):
        d = gcd(A[r,:].list())
        if not d == 0:
            A[r] /= d
        for c in xrange(A.dimensions()[1]):
            x = A[r,c]
            if 'simplify_full' in dir(x):
                A[r,c] = x.simplify_full()
            elif 'simplify_rational' in dir(x):
                A[r,c] = x.simplify_rational()
    return A


def getAllColines(M):
    """ (M)

        returns all colines of M (i.e. flats with rank rk(M)-2)"""
    colines = set()
    for flatbase in combinations(M.groundset(),M.rank()-2):
        cl = M.closure(flatbase)
        if M.rank(cl) == M.rank()-2:
            colines.add(cl)
    return colines

def getAllCopoints(M):
    """ (M)

        returns al copoints of M """
    copoints = set()
    for flatbase in combinations(M.groundset(),M.rank()-1):
        cl = M.closure(flatbase)
        if M.rank(cl) == M.rank()-1:
            copoints.add(cl)
    return copoints

def getPointsOnColine(M,coline):
    """ (M)

        returns all points of M, that are on a given coline"""
    copoints = getAllCopoints(M)
    coline = set(coline)
    return [P for P in copoints if coline.issubset(P)]

def positivityOfColines(M):
    """ (M)

        returns the difference of the number of simple copoints
        vs the number of non-simple(fat) copoints as dictionary per coline """
    colines = getAllColines(M)
    copoints = getAllCopoints(M)
    d = {}
    for L in colines:
        score = 0
        for P in copoints:
            if L.issubset(P):
                if len(P)-len(L) == 1:
                    score += 1
                else:
                    score -= 1
        d[L] = score
    return d


#********************
# gammoids
#********************


def pivotDigraph(D, e, b):
    """ (D, e, b)

        'pivots' D such that the sink b 'gives' its sink
        property to its in-neighbor e, which in turn
        becomes a sink of D then.
        (See fundamental theorem/matroid induction [Mason])

        works on/returns a copy of D
    """
    if not D.has_edge(e,b) or b not in D.sinks():
        return None
    Dp = copy.copy(D)
    for x in list(Dp.neighbors_out(e)):
        Dp.add_edge(b,x)
        Dp.delete_edge(e,x)
    Dp.add_edge(b,e)
    Dp.delete_edge(e,b)
    return Dp

def pivotsDigraph(D, *ps, **opts):
    """ (D, p1, p2, ..., verify=True)

        'pivots' D along p1, p2, ....

        optionally verifies, whether the pivot
        operation is admissible.

        works on/returns a copy of D
    """
    verify = True
    if "verify" in opts:
        verify = opts["verify"]
        opts.pop("verify")
    Dp = D
    for p in ps:
        last = None
        for x in reversed(p):
            if not last is None:
                if verify:
                    if not Dp.has_edge(x, last):
                        return "ERROR", Dp, " has no edge ", (x, last)
                Dp = pivotDigraph(Dp, x, last)
            last = x
    return Dp

def Gammoid(D, S=None, E=None):
    """
        (D, S=None, E=None)

         returns the gammoid wrt. to the digraph D,
         the set of sinks S,
         and the set of matroid elements E.

         If E==None, then E=V is used.
    """
    if type(D) != sage.graphs.digraph.DiGraph:
        D = DiGraph(D,loops=False)
    if E is None:
        E = list(D.vertices())
    if S is None:
        S = list(D.sinks())
    P = {}
    for e in E:
        P[e] = set()
    for p in D.all_simple_paths(E, S, trivial=True):
        e = p[0]
        P[e].add(frozenset(p))
    F0 = set()
    for e in E:
        for p in P[e]:
            F0.add((frozenset([e]),p))
    while F0:
        F1 = F0
        F0 = set()
        for (src,vtx) in F1:
            for e in E:
                if e in src:
                    continue
                for p in P[e]:
                    if not p.intersection(vtx):
                        F0.add((src.union( (e,) ), vtx.union(p)))
    bases = set()
    for src,vtx in F1:
        bases.add(src)
    return BasisMatroid(groundset=E, bases=bases)


def getDiGraphVariableToArcMap(D,S=None):
    """ (D, S=[])

        D __ *ACYCLIC* Digraph

       (S __ optional: sink set for gammoid)

        returns a dictionary which maps symbolic indefinites to arcs of D.
    """
    if type(D) != sage.graphs.digraph.DiGraph:
        D = DiGraph(D,loops=False)
    X, ordering = D.is_directed_acyclic(certificate=True)
    if not X:
        return "ERROR: Digraph D has to be acyclic!", ordering, " is a cycle!"
    if S is None:
        S = list(D.sinks())
    i = 0
    phi = {}
    for v in reversed(ordering):
        if v in S:
            continue
        for w in D.neighbors_out(v):
            phi[getVar(i)] = (v,w)
            i += 1
    return phi


def AcyclicGammoidLinearRepresentation(D, S=None, E=None, matrix=False, M=False, fancy=False, mat_dict=False):
    """ (D, S=None, E=None, matrix=False, M=False, fancy=False, mat_dict=False)

        D __ *ACYCLIC* Digraph
        S __ sinks
        E __ matroid elements

        matrix __ if true return matrix instead of dictionary
        M __ if true, return linear matroid for the matrix
        fancy __ if true, use 'speaking edge' variable names
        mat_dict __ if true, return a matrix and two dictionaries giving row and column
                    assignments

        returns a dictionary of vectors representing the gammoid represented by the
        _acyclic_ digraph D """
    if type(D) != sage.graphs.digraph.DiGraph:
        D = DiGraph(D,loops=False)
    X, ordering = D.is_directed_acyclic(certificate=True)
    if not X:
        return "ERROR: Digraph D has to be acyclic!", ordering, " is a cycle!"
    if E is None:
        E = list(D.vertices())
    if S is None:
        S = list(D.sinks())
    r = len(S)
    r0 = 0
    i = 0
    L = {}
    if mat_dict:
        row_assignment = {}
    for v in reversed(ordering):
        if v in S:
            x = Matrix(SR, r, 1)
            x[r0, 0] = 1
            if mat_dict:
                row_assignment[v] = r0
            r0 += 1
            L[v] = x
        else:
            x = Matrix(SR, r, 1)
            for w in D.neighbors_out(v):
                if fancy:
                    xi = SR.var("e_"+str(v)+str(w))
                else:
                    xi = getVar(i)
                x += L[w] * xi
                i += 1
            L[v] = x
    if matrix or M or mat_dict:
        LM = Matrix(SR, r, 0)
        if mat_dict:
            col_assignment = {}
            colnr = 0
        for e in E:
            LM = LM.augment(L[e])
            if mat_dict:
                col_assignment[e] = colnr
                colnr += 1
        if mat_dict:
            return LM, col_assignment, row_assignment
        if M:
            return LinearBasisMatroid(LM)
        return LM
    Ebar = frozenset(L.keys()).difference(E)
    for v in Ebar:
        L.pop(v)
    return L

def PathDigraph(*paths):
    """ (path1, path2, ...)

        creates a digraph from the paths given by the vertex lists.
    """
    A = {}
    for p in paths:
        last = None
        for x in p:
            if not x in A:
                A[x] = []
            if not last is None:
                A[last].append(x)
            last = x
    return DiGraph(A)

def getSimpleSinkPaths(D, S=None, V=None):
    """ (D, S=None, V=None)

        D __ digraph

        S __ optional, set of sinks
        V __ optional, set of start vertices

        returns all simple paths ending in sinks and starting in vertices of the gammoid
    """
    if type(D) != sage.graphs.digraph.DiGraph:
        D = DiGraph(D,loops=False)
    if S is None:
        S = list(D.sinks())
    if V is None:
        V = list(D.vertices())
    return D.all_simple_paths(V,S,trivial=True)


#****************
#   modpairs
#****************



def nonModularPairs(M):
    """ (M)

        returns a list of non-modular pairs of flats of the matroid M"""
    nmPairs = []
    for a,b in combinations(allFlats(M),2):
        if M.rank(a) + M.rank(b) > M.rank(a.union(b)) + M.rank(a.intersection(b)):
            nmPairs.append((a,b))
    return nmPairs


def nonTrivialCutGenerators(M):
    """ (M)

        returns all generators of non-trivial modular cuts of M"""
    f = []
    count =0
    for Mx in M.extensions("*"):
        count += 1;
        print "\rExtension nbr",count,
        sys.stdout.flush()
        J = [X.difference(["*"]) for X in allFlats(Mx) if "*" in X and Mx.rank(X.difference(["*"])) == Mx.rank(X)]
        print " .. ","%4d"%len(J),
        sys.stdout.flush()
        J0 = getMinimalFamily(J)
        print " .. ","%4d"%len(J0),"   ",
        if len(J0) > 1:
            if len(J0) == 2:
                print "\rFound non-trivial combination:",niceStr(J0)
            f.append(J0)
    return f

#****************
# setsystems
#****************


def mapViaGraph(G,x):
    """ (G,x)

        G __ arcs of a graph
        x __ vertex

        maps the element x to the end of the first arc that starts in x"""
    for s,t in G:
        if s == x:
            return t
    return None

def mapViaGraphInverse(G,x):
    """ (G,x)

        G __ arcs of a graph
        x __ vertex

        maps the element x to the start of the first arc that ends in x"""
    for t,s in G:
        if s == x:
            return t
    return None

def getCanonicalElementList(reqLen=None):
    """ (reqLen=None)

        returns a list of canonical names for elements; of requested length."""
    E = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890"
    if reqLen is None:
        return E
    if reqLen <= len(E):
        return E[:reqLen]
    return list(E) + list( xrange(10, reqLen-len(E)+10) )

def getCanonicalElement(nbr):
    """ (nbr)

        returns the label for the nbr-th canonical element """
    E = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890"
    if nbr <= len(E):
        return E[nbr-1]
    else:
        return int(nbr - len(E) + 10 - 1)

def getCanonicalId(x):
    """ (x)

        returns the nbr of the canonical element that is labeled by x """
    E = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890"
    if str(x) in E:
        return E.index(str(x)) + 1
    return len(E) + (int(x) -10) + 1

def isCanonicalSet(x):
    """ (x)

        test whether x only contains canonical labels"""
    E = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890"
    if not type(x) == frozenset:
        x = frozenset(x)
    for k in x:
        if k in E:
            continue
        try:
            q = int(k)
            if q < 10:
                return False
        except:
            return False
    return True

def canonicalizeSet(x):
    """ (x)

        map x to its canonical labels, if it is canonical. otherwise returns None."""
    l = []
    for k in x:
        E = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890"
        if str(k) in E:
            l.append(str(k))
            continue
        try:
            q = int(k)
            if q < 0:
                return None
            if q >= 10:
                l.append(q)
            else:
                l.append(str(q))
        except:
            return None
    return frozenset(l)

def reprCanonicalSet(x):
    """ (x)

        returns a number that represents a given canonical set in binary """
    if not type(x) == frozenset:
        x = frozenset(x)
    nbr = 0
    for k in x:
        nbr |=  1 << ((getCanonicalId(k)-1))
    return nbr

def dereprCanonicalSet(x):
    """ (x)

        turns a canonical representation back into a canonical label-set """
    if not type(x) == sage.rings.integer.Integer:
        x = sage.rings.integer.Integer(x)
    return frozenset(getCanonicalElement(i+1) for i,c in zip(xrange(x.nbits()),x.digits(2)) if c == 1)


def findSetSystemInjection(SRC,TRG,partial=None,all=False,induced=False):
    """ (SRC, TRG, partial=None, all=False, induced=False)

        find an injection of the sets in SRC into TRG, such that there is also an injection of elements

        partial is a partial set system injection that should be extended.
        """
    if partial == None:
        partial = ([],[],)
    if len(partial[0]) == len(SRC):
        return partial
    df = [x[0] for x in partial[0]]
    im = [x[1] for x in partial[0]]
    df_e = [x[0] for x in partial[1]]
    im_e = [x[1] for x in partial[1]]

    if all:
        combined = []

    for src in SRC:
        if src in df:
            continue
        for trg in TRG:
            if trg in im:
                continue
            if len(trg) < len(src):
                continue # impossible
            cont_outer = False
            src_e = []
            for x in src:
                if x in df_e:
                    if not mapViaGraph(partial[1],x) in trg:
                        cont_outer = True # trg cannot be the image of src
                        break
                else:
                     src_e.append(x)
            if induced:
                for x in trg:
                    if x in im_e:
                        if not mapViaGraphInverse(partial[1],x) in src:
                            cont_outer = True
                            break

            if cont_outer:
                continue

            trg_e = [x for x in trg if not x in im_e]
            if len(src_e) > len(trg_e):
                continue


            partial[0].append((src,trg))

            for src_im in itertools.permutations(trg_e, len(src_e)):
                if induced:
                    partmap = [(s,t) for s,t in zip(src_e,src_im)]
                    cont_outer = False
                    for sr,tg in partial[0]:
                        for x in tg:
                            if x in src_im:
                                if not mapViaGraphInverse(partmap,x) in sr:
                                    cont_outer = True
                                    break
                        if cont_outer:
                            break
                    if cont_outer:
                        continue


                for s,t in zip(src_e,src_im):
                    partial[1].append((s,t))


                m = findSetSystemInjection(SRC,TRG,partial,all,induced)

                if m != None:
                    if all:
                        combined.append(copy.deepcopy(m))
                    else:
                        return m

                for i in xrange(len(src_e)):
                    partial[1].pop()

            partial[0].pop()


    if all:
        return combined
    return None

def findSetSystemIsomorphismIncidenceStructure(A,B):
    """ (A,B)

        returns either None or a map phi, such that for all
        x in A, phi[x] in B; i.e. an isomorphism of Incidence Structures """
    As = sage.combinat.designs.incidence_structures.IncidenceStructure(A)
    Bs = sage.combinat.designs.incidence_structures.IncidenceStructure(B)
    phi = As.is_isomorphic(Bs,certificate=True)
    if phi == {}:
        return None
    return phi


def setSystemDigraph(A,X=None):
    """ (A, X=None)

        create a set system digraph for the family A;
        where X is the universe of the set system,
        X is set to  uniteAll(A)  if X is None (default)

        returns pair (Digraph, vertex mapping)
    """
    F = setFamilize(A)
    if X is None:
        X = uniteAll(F)
    Xl = sorted(X)
    Fl = sorted(sorted(f) for f in F)
    Fl = [frozenset(x) for x in Fl]
    Vmap = {}
    I = {}
    for i in xrange(len(Fl)):
        Vmap[i+1] = Fl[i]
        I[i+1] = []

    for i in xrange(len(Xl)):
        ix = -i-1
        x = Xl[i]
        Vmap[ix] = x
        I[ix] = []
        for j in xrange(len(Fl)):
            if x in Fl[j]:
                I[ix].append(j+1)

    return DiGraph(I),Vmap


def findSetSystemIsomorphismDigraph(A, B):
    """ (A,B)

        returns either None or a map phi, such that for all
        x in A, phi[x] in B; i.e. an isomorphism of Incidence Structures;
        uses Digraphs """
    if len(A) != len(B):
        return None
    Da, Va = setSystemDigraph(A)
    Db, Vb = setSystemDigraph(B)
    r, phi = Da.is_isomorphic(Db,certify=True)
    if not r:
        return None
    psi = {}
    for x in phi.keys():
        if x >= 0:
            continue
        psi[Va[x]] = Vb[phi[x]]
    return psi


def findSetSystemIsomorphismRecursive(A, B):
    """ (A,B)

        returns either None or a map phi, such that for all
        x in A, phi[x] in B; i.e. an isomorphism of Incidence Structures;
        uses recursion on partial phi's """
    if len(A) != len(B):
        return None
    F = setFamilize(A)
    G = setFamilize(B)
    E_F = uniteAll(F)
    E_G = uniteAll(G)
    if len(E_F) != len(E_G):
        return None
    degrees_F = {}
    degrees_G = {}
    for e in E_F:
        d = sum(1 for f in F if e in f)
        if d in degrees_F:
            degrees_F[d].append(e)
        else:
            degrees_F[d] = [e]
    for e in E_G:
        d = sum(1 for f in G if e in f)
        if d in degrees_G:
            degrees_G[d].append(e)
        else:
            degrees_G[d] = [e]
    if frozenset(degrees_F.keys()) != frozenset(degrees_G.keys()):
        return None
    for k in degrees_F.keys():
        if len(degrees_F[k]) != len(degrees_G[k]):
            return None
    K = sorted(degrees_F.keys())
    def completePartialMap(phi={},image=tuple()):
        complete = True
        for k in K:
            for e in degrees_F[k]:
                if not e in phi:
                    complete = False
                    break
            if not complete:
                break
        if complete:
            return phi
        for c in degrees_G[k]:
            if c in image:
                continue
            phi[e] = c
            Fphi = [frozenset([phi[x] for x in X if x in phi]) for X in F]
            Gimage = [frozenset([x for x in X if x == c or x in image]) for X in G]
            if frozenset(Fphi) == frozenset(Gimage):
                for X in frozenset(Fphi):
                    if sum(1 for f in Fphi if f == X) == sum(1 for g in Gimage if g == X):
                        px = completePartialMap(phi,image+(c,))
                        if not px is None:
                            return px
            phi.pop(e)
        return None
    return completePartialMap()



# We measured with
#    time createFamilyClassListExtend(12,4,3,justtime=True)
#
#   findSetSystemIsomorphismRecursive
#       CPU times: user 4min 39s, sys: 373 ms, total: 4min 40s
#       Wall time: 4min 40s
#
#   findSetSystemIsomorphismIncidenceStructure
#       CPU times: user 4.78 s, sys: 36.2 ms, total: 4.82 s
#       Wall time: 4.86 s
#   findSetSystemIsomorphismDigraph
#       CPU times: user 6.17 s, sys: 37.6 ms, total: 6.2 s
#       Wall time: 6.24 s
#
#   streamlining IncidenceStructure into createFamilyClassListExtend:
#       CPU times: user 3.89 s, sys: 32.5 ms, total: 3.92 s
#       Wall time: 3.97 s
#
findSetSystemIsomorphism = findSetSystemIsomorphismIncidenceStructure
#*************
# transversal
#*************


def getMaximalPartialTransversals(T):
    """ (T)

        T __ family of subsets of some groundset


        returns maximal (partial) transversals for T"""
    if type(T) == type({}):
        T = T.values()
    pTs = set([frozenset()])
    for A in T:
        augmented = set()
        for e in A:
            for X in pTs:
                if e in X:
                    continue
                Xe = frozenset( (e,) ).union(X)
                augmented.add(Xe)
        if len(augmented):
            pTs = augmented
    return pTs

#********************
#   violations
#********************


def findViolations(M):
    """ (M)

        check the antichain families of cyclic flats for violations """
    groundset = M.groundset()
    Z = set([frozenset()]).union(*M.circuit_closures().values()) # -> cyclic flats
    V = []
    for Z0 in nonEmptyAntiChains(Z):
        if slack(M,Z0) < 0:
            V.append(Z0)
    return V

def deltaRestrictions(M,verbose=False):
    """ (M,verbose=False)

        find lower bounds on the delta values of antichains of cyclic flats. """
    groundset = M.groundset()
    Z = set([frozenset()]).union(*M.circuit_closures().values()) # -> cyclic flats
    V = []
    for Z0 in nonEmptyAntiChains(Z):
        V.append((Z0, -slack(M,Z0)))
        if verbose:
            print niceStr(V[-1][0]), " >= ", V[-1][1]
    return V

def analyzeDeletionSlackValues(M,x):
    """ (M,x)

        analyze deletions for slack values... """
    groundset = M.groundset()
    Z = set([frozenset()]).union(*M.circuit_closures().values()) # -> cyclic flats
    Zdisappear = set()
    for z in Z:
        if M.rank(z) == len(z)-1 and x in z:
            print niceStr([z]),"dis-cyclifies."
            Zdisappear.add(z)
    Mx = M.delete(x)
    print "Deleting from Z(M):"
    idx = 1
    for Z0 in nonEmptyAntiChains(Z.difference(Zdisappear)):
        s0 = slack(M,Z0)
        s1 = slack(Mx,[z.difference(set(x)) for z in Z0])
        print idx, "d",niceStr(Z0),"= ",s1,"-",s0,"=",s1-s0
        idx += 1
    print "Closing from Z(M-x):"
    idx = 1
    Z = set([frozenset()]).union(*Mx.circuit_closures().values()) # -> cyclic flats
    for Z1 in nonEmptyAntiChains(Z.difference(Zdisappear)):
        Z0 = [M.closure(z) for z in Z1]
        s0 = slack(M,Z0)
        s1 = slack(Mx,[z.difference(set(x)) for z in Z0])
        print idx, "d",niceStr(Z1),"- d",niceStr(Z0),"= ",s1,"-",s0,"=",s1-s0
        idx += 1


def checkAlpha(M,complete=False,negativeKeys=False):
    """ (M,complete=False,negativeKeys=False)


        calculate alpha values for all subsets of E(M),
        stop, if for some subset, alpha < 0;
        unless complete=True """
    groundset = M.groundset()
    a = {} # -> alpha values
    Z = set([frozenset()]).union(*M.circuit_closures().values()) # -> cyclic flats
    if negativeKeys:
        negKeys = []
        complete = True
    for X in powerset(groundset):
        X = frozenset(X)
        subsum = 0
        for z in Z:
            if z.issubset(X) and not X == z:
                subsum += a[z]
        a[X] = len(X) - M.rank(X) - subsum
        if a[X] < 0:
            if not complete:
                kill_list = [] # remove verbose part of the matroid
                for Y in a:
                    if not Y.issubset(X):
                        kill_list.append(Y)
                for Y in kill_list:
                    del a[Y]
                return a #early exit
            elif negativeKeys:
                    negKeys.append(X)
    if negativeKeys:
        return a, negKeys
    return a

def cyflatFamilyFor(M, X, Z=None):
    """ (M, X, Z=None)

        returns the maximal proper subflats that are cyclic (!better double check code!)
        """
    if type(X) != frozenset:
        X = frozenset(X)
    groundset = M.groundset()
    if Z == None:
        Z = set([frozenset()]).union(*M.circuit_closures().values()) # -> cyclic flats
    Q = []
    for z in Z:
        if z.issubset(X) and not X == z:
            dominated = False
            for q in Q:
                if z.issubset(q):
                    dominated = True
                    break
            if not dominated:
                Q = [q for q in Q if not q.issubset(z)] + [z]
    return frozenset(Q)

def slack(rk,Z,verbose= False):
    """ (rk,Z,verbose= False)

        rk __ rank function or Matroid object

        Z  __ family of cyclic flats

        calculates the slack of Z wrt. to a rank function (or a matroid) """

    if "rank" in dir(rk):
        rk = rk.rank
    s = -rk(uniteAll(Z))
    if verbose:
        print "rk(U Z) = ",-s
        global slack_stats
        slack_stats = {}
    for Zp in powersetMinusO(Z):
        if verbose:
            k = (len(Zp), rk(intersectAll(Zp)))
            if not k in slack_stats:
                slack_stats[k] = 1
            else:
                slack_stats[k] = slack_stats[k]+1
        if (len(Zp)) % 2 == 1:
            s += rk(intersectAll(Zp))
            if verbose:
                print "summand for ",niceStr(Zp)," +rk("+niceStr([intersectAll(Zp)])+ ") = +",rk(intersectAll(Zp))
        else:
            s -= rk(intersectAll(Zp))
            if verbose:
                print "summand for ",niceStr(Zp)," -rk("+niceStr([intersectAll(Zp)])+ ") = -",rk(intersectAll(Zp))
    return s


def violations(M,a=None,x=None):
    """ (M,a=None,x=None)

        M __ matroid

        a __ (optional) alpha value dictionary
        x __ (optional) must be given if alpha is given, set of keys where a[z] < 0 (any flats)

        returns all families of cyclic flats that are violating the strict gammoid inequalities.
        (by finding the representations for the negative alpha keys)
            (well, better check the code again!)
        """
    if a == None:
        a,x = checkAlpha(M,negativeKeys=True)
    Zs = uniq([cyflatFamilyFor(M,y) for y in x])
    Zs = [z for z in Zs if slack(M,z) < 0]
    return Zs

def freeSlackVector(Z):
    """ (Z)

        returns a 'sum term dict' that corresponds to the slack of a given family, where the rank function is free (a variable)"""
    A = setFamilize(Z)
    s = {uniteAll(A): -1}
    for Zp in powersetMinusO(A):
        if (len(Zp)) % 2 == 1:
            X = intersectAll(Zp)
            if X in s:
                s[X] = s[X] + 1
            else:
                s[X] = 1
        else:
            X = intersectAll(Zp)
            if X in s:
                s[X] = s[X] - 1
            else:
                s[X] = -1
    #cancel out zeros and emptyset
    d = {}
    for x in s:
        if len(x) == 0:
            continue
        if s[x] != 0:
            d[x] = s[x]
    return d

def niceFreeVector(d):
    """ (d)

        nice string repr. for a free sum term dictionary """
    s = []
    for x in d:
        if d[x] == 0:
            continue
        xn = "".join(map(str,sorted(x)))
        s.append((len(x), xn, d[x]))
    s.sort()
    s = [" %+d*rk(%s)"%(x[2],x[1]) for x in s]
    return "".join(s)


#********
# fca
#********

def subsetVector(A,B):
    """ (A,B)

        A, B __ vectors whose elements evaluate to true/false

        checks whethere A is a subset of B.
    """
    for a,b in zip(A,B):
        if a:
            if not b:
                return False
    return True


def getFlatLatticeStandardContext(M):
    """ (M)

        M __ matroid

        returns (G,M,I) of the standard context of the lattice of flats of
                the matroid M. The set G corresponds to rank-1 flats (atoms),
                and the set M corresponds to rank-(r-1) flats (hyperplanes, coatoms),
                whereas I corresponds to the subset relation between G and M.

            where G, M are lists of objects and attributes, resp.,
            and I is a tuple of row-tuples of I, so if
            g = G[i] and m = M[j], then
            I[i][j] == True  iff  gIm in the context.
    """
    G = tuple(sorted(( tuple(sorted(F)) for F in M.flats(1) )))
    M = tuple(sorted(( tuple(sorted(H)) for H in M.flats(M.rank()-1) )))
    I = []
    for g in G:
        gI = []
        for m in M:
            if frozenset(g).issubset(m):
                gI.append(True)
            else:
                gI.append(False)
        I.append(tuple(gI))
    return G,M,tuple(I)

def transposeTupleTuple(I):
    """ (I)

        I __ tuple of tuples.

        returns a tuple of tuples, where the i-th tuple
            corresponds to the i-th entries of the tuples of I
    """
    J = [[] for i in range(len(I))]
    for r in I:
        for c, idx in zip(r, range(len(r))):
            J[idx].append(c)
    return tuple((tuple(x) for x in J))


def calculateArrowRelation(G,M,I):
    """ (G,M,I)

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
    """
    J = []
    IT = transposeTupleTuple(I)
    for g,idxg in zip(G,range(len(G))):
        gJ = []
        gI = I[idxg]
        for m,idxm in zip(M,range(len(M))):
            if gI[idxm]:
                gJ.append(0)
            else:
                downarrow = True
                for hI in I:
                    if subsetVector(gI,hI):
                        if subsetVector(hI,gI):
                            continue
                        if not hI[idxm]:
                            downarrow = False
                            break
                uparrow = True
                mI = IT[idxm]
                for nI in IT:
                    if subsetVector(mI,nI):
                        if subsetVector(nI,mI):
                            continue
                        if not nI[idxg]:
                            uparrow = False
                            break

                if downarrow:
                    if uparrow:
                        gJ.append(3)
                    else:
                        gJ.append(1)
                else:
                    if uparrow:
                        gJ.append(2)
                    else:
                        gJ.append(0)
        J.append(tuple(gJ))

    return tuple(J)

def reduceDoubleFoundedContext(G,M,I):
    """ (G, M, I)

        (G,M,I) __ formal context,

            where G, M are lists of objects and attributes, resp.,
            and I is a tuple of row-tuples of I, so if
            g = G[i] and m = M[j], then
            I[i][j] == True  iff  gIm in the context.

        returns the reduced context (G',M',I') consisting only of
                irreducible objects and attributes, and their respective
                relations
    """
    J = calculateArrowRelation(G,M,I)
    JT = transposeTupleTuple(J)
    Gp = []
    Gi = []
    Mp = []
    Mi = []
    for g,i in zip(G,range(len(G))):
        irreducible = False
        for x in J[i]:
            if x == 1 or x == 3:
                irreducible = True
                break
        if irreducible:
            Gp.append(g)
            Gi.append(i)
    for m,i in zip(M,range(len(M))):
        irreducible = False
        for x in JT[i]:
            if x == 2 or x == 3:
                irreducible = True
                break
        if irreducible:
            Mp.append(m)
            Mi.append(i)
    Ip = tuple(( tuple(( I[i][j] for j in Mi)) for i in Gi ))
    return Gp, Mp, Ip

def getBurmeisterString(G,M,I,name="unnamed"):
    """ (G,M,I, name="unnamed")


        (G,M,I) __ formal context,

            where G, M are lists of objects and attributes, resp.,
            and I is a tuple of row-tuples of I, so if
            g = G[i] and m = M[j], then
            I[i][j] == True  iff  gIm in the context.

        name __ optional name of the context

        returns the corresponding Burmeister context file.
    """
    txt = ["B",str(name),str(len(G)), str(len(M))] + \
          [str(g) for g in G] + [str(m) for m in M]
    for r in I:
        rTxt = ""
        for c in r:
            if c:
                rTxt += "X"
            else:
                rTxt += "."
        txt.append(rTxt)
    return "\n".join(txt)

def saveBurmeisterContext(G,M,I,filename):
    """ (G,M,I, filename)


        (G,M,I) __ formal context,

            where G, M are lists of objects and attributes, resp.,
            and I is a tuple of row-tuples of I, so if
            g = G[i] and m = M[j], then
            I[i][j] == True  iff  gIm in the context.

        filename __ path where context is stored,
                make it end with ".cxt" in order to open it with ConExp...
    """
    with open(filename,"wt") as f:
        f.write(getBurmeisterString(G,M,I,filename))
        f.close()

##### diss.spyx


def getAlphaSystem(M):
    """
        (M)
        calculate the alpha-transversal system of M"""
    alpha = {}
    for x in allFlats(M):
        nlt = len(x) - M.rank(x)
        for y in alpha:
            if y.issubset(x):
                nlt -= alpha[y]
        alpha[x] = nlt
    delkeys = [x for x in alpha if alpha[x] == 0]
    for k in delkeys:
        del alpha[k]
    return alpha

def TransversalMatroid(A,groundset=None):
    """
        A __ family of subsets of the groundset E


        returns a BasisMatroid where the independent sets correspond to the
                partial transversals of the family A
    """
    A = [frozenset(x) for x in A]
    if groundset is None:
        groundset = uniteAll(A)
    bases = set([frozenset()])
    for Ai in A:
        new_bases = set()
        augments_one = False
        for B0 in bases:
            for x in Ai:
                if not x in B0:
                    augments_one = True
                    new_bases.add(B0.union([x]))
        if augments_one:
            bases = new_bases

    return BasisMatroid(bases=bases,groundset=groundset)

def getAlphaTMatroid(M):
    """
        (M)

        M __ matroid

        returns the transversal matroid of all partial transversals of \mathcal{A}_M;
        where we rather ignore negative alpha values.
    """
    alpha = getAlphaSystem(M)
    A = []
    for X in alpha:
        for i in range(0,alpha[X]):
            A.append(X)
    return TransversalMatroid(A, M.groundset())



def prnF(X):
    """(X)

        X __ list of sets

        prints the contents of X sorted by their setStr representation
    """
    for x in sorted([setStr(x) for x in X]):
        print x

def allDependentFlats(M):
    """ (M)

        M __ matroid

        returns an iterator of all dependent flats of M
    """
    return filter(lambda F: M.rank(F) < len(F), allFlats(M))

def outerMargin(D, X):
    """ (D,X)

        D __ digraph
        X __ set of vertices

        returns the outer-margin of X, i.e.
            the vertices that can be reached from vertices in X,
            but that are not contained in X.
    """
    clX = set( (v for (u,v,l) in D.outgoing_edges(X)))
    return clX.difference(X)

def getRightmostBase(F,D,T):
    """ (F,D,T)

        F __ flat of the strict gammoid for (D,T),
             subset of the vertices of D
        D __ digraph
        T __ set of (gammoid) sinks

        returns the unique rightmost base of F wrt. (D,T)
    """
    F = frozenset(F)
    return outerMargin(D,F).union(F.intersection(T))

def getRightmostBaseMap(D,T,M=None):
    """ (D,T, M=None)
        D __ digraph
        T __ set of (gammoid) sinks
        M __ (optional) Gammoid(D,T)

        returns a dictionary that maps all dependent flats to its rightmost bases
    """
    if M is None:
        M = Gammoid(D,T)
    phi = {}
    for F in allDependentFlats(M):
        phi[F] = getRightmostBase(F,D,T)
    return phi

def getFlatBases(M,F):
    """ (M,F)

        M __ matroid
        F __ flats

        returns all bases of the flat F
    """
    return set(M.delete(M.groundset().difference(F)).bases())

def incrementByOne(now,ends):
    """ (now, ends)

        now  __ (rw-array) current position
        ends __ strict upper-bounds for each now[i]

        increments the now array by one; where elements with higher index
                   have lower significance.
            if for some index the upper bound is it, it is replaced by 0
            and the next more significant index is incremented by one...

        returns the lowest index that has been set to zero
                (return value might point out of the array!)
    """
    i = len(now) - 1
    now[i] += 1
    while now[i] >= ends[i]:
        now[i] = 0
        i -= 1
        if i < 0:
            return 0
    return i+1

def findPossibleRightmostBaseMap(M):
    """ (M)

        M __ matroid

        returns a rightmost base map; if there is one;
        otherwise returns False
    """
    dF = sorted(allDependentFlats(M),key=M.rank)
    rB = [list(getFlatBases(M,F)) for F in dF]
    checkIdxs = [(i,j) for j in range(len(dF)) for i in range(j) if dF[i].issubset(dF[j])]
    checkIdxs.sort(key=max)
    print len(dF),"dependent flats"
    nChoices = 1
    for x in rB:
        nChoices *= len(x)
    print nChoices,"candidates for rightmost base maps"
    print len(checkIdxs),"constraint pairs"
    candidate = [0 for i in range(len(dF))]
    checked = False
    empty = frozenset()
    while not checked:
        all_good = True
        for i,j in checkIdxs:
            if not all_good:
                break
            phiF1 = rB[i][candidate[i]]
            phiF2 = rB[j][candidate[j]]
            delta = phiF1.difference(phiF2)
            if delta == empty:
                continue
            for k in range(len(dF)):
                phiG = rB[k][candidate[k]]
                if phiF2.issubset(phiG):
                    if delta.intersection(phiG) != empty:
                        # we violate the right-most property here
                        all_good = False
                        # Fun fact: this is B. Ganter's Next Closure Technique
                        # if we increment candidate[x],
                        # we have to set candidate[x+1:] = [0,0,..,0]
                        ends = [len(rB[i]),len(rB[j]),len(rB[k])]
                        now = [candidate[i],candidate[j],candidate[k]]
                        solved = False
                        while not solved:
                            x1 = incrementByOne(now,ends)
                            if x1 == 0:
                                return False
                            phiF1 = rB[i][now[0]]
                            phiF2 = rB[j][now[1]]
                            phiG = rB[k][now[2]]
                            solved = True
                            if phiF2.issubset(phiG):
                                if (phiF1.difference(phiF2)).intersection(phiG) != empty:
                                    solved = False
                        # fill in solution
                        for q in range(x1,len(rB)):
                            candidate[q] = 0
                        candidate[i] = now[0]
                        candidate[j] = now[1]
                        candidate[k] = now[2]
                        break

        checked = all_good
    phi = {}
    for (F,B,i) in zip(dF,rB,candidate):
        phi[F] = B[i]
    return phi



def hasSubsetSubimageProperty(phi):
    """ (phi)

        phi __ map that maps sets to setStr

        return Test, if for X,Y with X.issubset(Y) the property
                phi[X].issubset(phi[Y]) holds. Returns a list of
                counterexample 4-tuples (X,Y,phi[X],phi[Y]);
                or an empty list if the property holds.
    """
    counterexs = []
    for X in phi:
        for Y in phi:
            if X.issubset(Y):
                if not (phi[X]).issubset(phi[Y]):
                    counterexs.append((X,Y,phi[X],phi[Y]))
    return counterexs


def printMasonAlpha(M):
    """ (M)
        print the alpha system
        """
    alpha = getAlphaSystem(M)
    for X in sorted(alpha.keys(),cmp=lambda x,y: len(x) - len(y)):
        print setStr(X), "a=",alpha[X]

### oriented circuit stuff

def pivotColOps(A,row, column=None, unity=False, Z=True, simplify=False):
    """ (A, row, column=None, unity=False, Z=True, simplify=False)

        pivot on row, column in A;

        using COLUMN operations

        optionally making the pivot element 1.

        Z __ pivot in the ring of integers using lcm


        simplify __ if true, call simplify() or simplify_full() on
                    each rows value, if available


        works on/returns a copy of A
    """
    Ap = copy.copy(A)
    if column is None:
        for i in xrange(Ap.dimensions()[1]):
            if Ap[row,i] != 0:
                column = i
                break
        if row is None:
            return "Error, cannot pivot-in zero-row %d"%column
    if unity and not Z:
        Ap[:,column] /= Ap[row,column]
    for i in xrange(Ap.dimensions()[1]):
        if i == column:
            continue
        if Z:
            cm = lcm(Ap[row,i], Ap[row,column])
            if cm != 0:
                a = (cm / Ap[row,i])
                if 'simplify_rational' in dir(a): # polynomials need manual cancelling
                    a = a.simplify_rational()
                b = (cm / Ap[row,column])
                if 'simplify_rational' in dir(b):# polynomials need manual cancelling
                    b = b.simplify_rational()
                Ap[:,i] = a*Ap[:,i] - b*Ap[:,column]
        else:
            Ap[:,i] -= (Ap[row,i]/Ap[row,column])* Ap[:,column]
        if simplify:
            for r in xrange(Ap.dimensions()[0]):
                x = Ap[r,i]
                if 'simplify_full' in dir(x):
                    Ap[r,i] = x.simplify_full()
                elif 'simplify' in dir(x):
                    Ap[r,i] = x.simplify()
    return Ap

def getIndetMatrix(n,r):
    """ (n,r)

        n __ elements (= number of rows)
        r __ rank (= number of columns)

        returns a matrix filled with variables that resembles the shape of
                a matrix representing a given matroid on n elements and rank r
    """
    return Matrix(n,r,var([chr(ltr)+str(nbr) for ltr in range(ord('a'),ord('a')+n)
                                    for nbr in range(1,r+1)]))



def getLeadingMonomial(term,order):
    """ (term,order)

        term  __ some term containing variables
        order __ tuple/list that prioritizes some variables over others.

        returns the leading monomial of term wrt. order.
    """
    vs = term.variables()
    relevant_order = [o for o in order if o in vs]
    T = term
    for x in relevant_order:
        coe,pwr = T.coefficients(x)[-1]
        T = coe * x**pwr
    return T
##############

def allRoutingsBetween(D,T,E):
    """ (D,T,E)

        D __ digraph
        T __ (gammoid) sinks
        E __ routing sources

        returns the set of routings from E to T in D;
               where a routing consists of a set of paths
               such no two paths do not have a common vertex
    """
    paths = set((tuple(x) for x in D.all_simple_paths(E,T,trivial=True)) )
    head = set([ (frozenset(), frozenset()) ])
    routings = set([ frozenset() ])
    while head:
        new_head = set()
        for R,V in head:
            for p in paths:
                if V.intersection(p):
                    continue
                R2 = R.union((p,))
                V2 = V.union(p)
                if R2 in routings:
                    continue
                routings.add(R2)
                new_head.add((R2,V2))
        head = new_head
    return routings

def getPathArcSet(p):
    """ (p)

        p __ path (tuple or list)

        returns the set of arcs of p
    """
    return frozenset(( (p[i],p[i+1]) for i in range(0,len(p)-1)))

def getArcSet(R):
    """ (R)

        R __ list of paths

        returns the combined arc set of the paths in R
    """
    return uniteAll((getPathArcSet(p) for p in R))

def cmpRs(R1,R2,cmp=cmp):
    """ (R1,R2, cmp=cmp)

        R1, R2 __ routings

        cmp __ comparison function for the arcs

        return a comparison between R1 and R2,
        where the routing that contains the biggest arc that the other
        routing does not posess, wins"""
    X1 = getArcSet(R1)
    X2 = getArcSet(R2)
    D1 = X1.difference(X2)
    D2 = X2.difference(X1)
    ordered = sorted(list(D1)+list(D2),cmp=cmp)
    if not ordered:
        return int(0)
    if ordered[-1] in X2: #X2 is biggest
        return int(-1)
    return int(1)

def getMaximalRouting(X, Rs, cmpRs=cmpRs):
    """ (X, Rs, cmpRs=cmpRs)

        X  __ source set
        Rs __ list/set of routings

        cmpRs __ comparison function for the routings

        returns the routing starting in X that is maximal
            with respect to the arc order.
        [this uses the natural order on the arcs]
    """
    X = frozenset(X)
    candidates = [R for R in Rs if frozenset((p[0] for p in R))==X ]
    candidates.sort(cmp=cmpRs)
    if not candidates:
        return None
    return candidates[-1]

def formatRouting(R,headline=None,cmp=cmp):
    """ (R, headline=None, cmp=cmp)

        R __ routing


        cmp __ comparison function for the natural ordering of sources and sinks
               (used to determine the sign of the permutation)

        returns an array of strings that displays the routing
    """
    OUT =[]
    if headline:
        OUT = [headline]
    maxLen = max((len(p) for p in R))
    ST = [(p[0],p[-1],p) for p in R]
    T = [p[-1] for p in R]
    ST.sort(cmp=cmp)
    T.sort(cmp=cmp)
    P = Permutation([T.index(x[1])+1 for x in ST])
    OUT.append("sgn(R) = %+d"%(P.sign()))
    OUT += combineCols([[p[i-(maxLen-len(p))] if i >= maxLen-len(p) else ""
                                for i in range(maxLen)]
                        for x,y,p in ST],nspaces=1,sep="|")
    #OUT += [ST[0][2]]
    return OUT

def sgnR(R, cmp=cmp):
    """ (R)

        R __ routing

        cmp __ comparison function for the natural ordering of sources and sinks


        returns the sign of R with respect to the builtin ordering in python
    """
    ST = [(p[0],p[-1]) for p in R]
    T = [p[-1] for p in R]
    ST.sort(cmp=cmp)
    T.sort(cmp=cmp)
    P = Permutation([T.index(x[1])+1 for x in ST])
    return P.sign()


def combineCols(COLS,nspaces=2,ch=" ",sep=" "):
    """ (COLS, nspaces=2,ch=" ",sep=" ")

        COLS __ an array of column arrays


        nspaces __ number of spaces between the columns
             ch __ fill spacing character
            sep __ last spacing character

        returns an array of strings where all columns from COLS have between
            collated together.
    """
    RESULT = ["" for i in range(max((len(c) for c in COLS)))]
    for c in COLS:
        l = max((len(str(x)) for x in c))+nspaces
        for i in range(len(RESULT)):
            x0 = "" if i >= len(c) else str(c[i])
            for j in range(len(x0), l-1):
                x0 += ch
            if l > 0:
                x0 += sep
            RESULT[i] += x0
    return RESULT

def printCols(COLS):
    """ (COLS)

        COLS __ columns

        quick print the columns to the screen
    """
    print "\n".join(combineCols(COLS))



def ssetStr(X):
    """ (X)

        X __ a signed set, i.e. S consists of tuples
            (s,sgn) where sgn is either 1 or -1

        returns a nice string representing the signed set
    """
    s = []
    for x in X:
        s.append((str(x[0]),"-" if x[1] < 0 else ""))
    s.sort(cmp=lambda x,y:niceCmp(x[0],y[0]) )
    return "{"+",".join(map(lambda x: x[1] +x[0], s))+ "}"

def getSignedCircuits(D,T,E, negativeArcs=[], cmp=cmp, verbose=sys.stdout):
    """ (D,T,E, negativeArcs=[], cmp=cmp, verbose=None)

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
    """
    M = Gammoid(D,T,E)
    Rs = allRoutingsBetween(D,T,E)
    negativeArcs = frozenset(negativeArcs)
    Cs = set()
    for C in M.circuits():
        print >>verbose,"\nCircuit: ",setStr(C)
        COLS = []
        sgns = []
        Csort = sorted(C,cmp=cmp)
        for c in Csort:
            Cc = C.difference([c])
            R = getMaximalRouting(Cc,Rs, cmpRs=lambda x,y: cmpRs(x,y,cmp=cmp))
            COLS.append(formatRouting(R,"C("+str(c)+") = ",cmp=cmp))
            nRA = negativeArcs.intersection(((p[i],p[i+1]) for p in R for i in range(len(p)-1) ))
            if len(nRA) % 2 == 0:
                sgns.append(sgnR(R))
            else:
                sgns.append(-sgnR(R))
        sC = [-sgns[0]] + [-sgns[i] if i%2 == 0 else sgns[i] for i in range(1,len(sgns))]
        c0 = set()
        c1 = set()
        for i in range(len(sC)):
            c0.add((Csort[i],sC[i]))
            c1.add((Csort[i],-sC[i]))
            COLS[i][0] += "%+d"%sC[i]
        print >>verbose, "\n".join(combineCols(COLS))
        Cs.add(frozenset(c0))
        Cs.add(frozenset(c1))

    return M,Rs,frozenset(Cs)

def checkOMAxiomC4p(C):
    """ (C)
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
    """
    counterexamples = []
    for c0,c1 in itertools.combinations(C,2):
        minusc0 = frozenset(((e,-s) for e,s in c0))
        if c1 == minusc0:
            continue
        for (e,s) in c0:
            if (e,-s) in c1:

                allowedSupport = c0.union(c1).difference( ((e,s),(e,-s)) )
                found = False
                for z in C:
                    if allowedSupport.issuperset(z):
                        found = True
                        break
                if not found:
                    counterexamples.append((c0,c1,e))
                    print "Cannot eliminate",e,"in",ssetStr(c0),"and",ssetStr(c1)
    return counterexamples


def testCombinatorialOrientation(D,T,E,cmp=cmp,maxN=8200):
    """ (D,T,E, cmp=cmp, maxN=8200)

        D __ digraph
        T __ target vertices
        E __ groundset of the Gammoid

        cmp  __ comparison function for arc and vertex orders
        maxN __ number of test cases that triggers random testing


        tests random combinatorial orientations of D,T,E

    returns error, C,negativeArcs

    """


    allArcs = frozenset((a,b) for a,b,l in D.edges())

    print "Checking random weight assignments for (C4')"
    error =False
    runcount = 0

    NUL = open("/dev/null","wt")

    SubsetOfAllArcs = Subsets(allArcs)
    if len(SubsetOfAllArcs) < maxN:
        print "Test all",len(SubsetOfAllArcs),"combinations"
        testall=True
    else:
        print "Random test with",maxN,"replications."
        testall=False

    while not error:
        print runcount,"runs without counterexample."

        if testall == False:
            print "Trying random negative arcs:"

            negativeArcs = sorted(SubsetOfAllArcs.random_element())
            print "  negative =",setStr(negativeArcs)
        else:
            print "Testing ",runcount, " of ", len(SubsetOfAllArcs)
            negativeArcs = SubsetOfAllArcs[runcount]


        sys.stdout.flush()
        M,R,C = getSignedCircuits(D,T,E,negativeArcs,verbose=NUL,cmp=cmp)
        error = checkOMAxiomC4p(C) != []
        if not error:
            print "     ..valid OM"
        runcount += 1
        if runcount >= min(maxN, len(SubsetOfAllArcs)):
            break

    if error:
        print "Found a problem! Investigate with \n error,C,negativeArcs = _"
    else:
        print "All good. ( ^^)"

    return error, C, negativeArcs


def liftDipathCycle(D, c=None, x0=None, t0=None):
    """ (D, c=None, x0=None, t0=None):

        D __ Digraph

        optional argument:
        c   __ cycle path in D
        x0  __ name of the new non-sink vertex in D
        t0  __ name of the new sink vertex in D


        returns a DiGraph that is the lifting of the cycle c, x0, t0;
                if no cycle is given and D does not contain a cycle,
                returns D itself.
    """
    if c is None:
        Cs = D.all_simple_cycles()
        if len(Cs):
            c = Cs[0]
        else:
            return D
    takenNames = set(Dx.vertices()+[x0,t0])
    if x0 is None or t0 is None:
        idx = 1
        while "x%d"%idx in takenNames or "t%d"%idx in takenNames:
            idx += 1
        if x0 is None:
            x0 = "x%d"%idx
        if t0 is None:
            t0 = "t%d"%idx
    Dl = copy.copy(D)
    Dl.delete_edge(c[0],c[1])
    Dl.add_edge(c[0],t0)
    Dl.add_edge(x0,t0)
    Dl.add_edge(x0,c[1])
    return Dl

def sniceStr(X,sep=",\n "):
    """ (X,sep=",\n "):
        X __ family of signed Subsets

        sep __ separator between each signed subset

        returns a nicely formatted string
    """
    s = [(sorted((y[0] for y in x)),x) for x in X]
    s.sort()
    return "{"+sep.join(map(lambda x: ssetStr(x[1]), s))+"}"

def contractSignedCircuitsTo(C, F):
    """ (C,F)

        C __ family of signed circuits
        F __ set to contract C to

        returns C|'F, the contraction of C to F
    """
    F = frozenset(F)
    Cp = set()
    Csupports = set()
    for c in (frozenset((a,s) for a,s in c0 if a in F) for c0 in C):
        if c == frozenset():
            continue
        csup = frozenset((a for a,s in c))
        is_minimal = True
        for cs2 in Csupports:
            if cs2.issubset(csup) and cs2 != csup:
                is_minimal = False
                break
        if is_minimal:
            Csupports = set([csup]+[cs for cs in Csupports if not csup.issubset(cs)])
            Cp = set([c]+[cq for cq in Cp if frozenset((a for a,s in cq)) in Csupports])
    return Cp

def restrictSignedCircuitsTo(C, F):
    """ (C,F)

        C __ family of signed circuits
        F __ set to contract C to

        returns C|F, the restriction of C to F
    """
    F = frozenset(F)
    return set(c for c in C if F.issuperset((a for a,s in c)))

def CircuitBasisMatroid(circuits,groundset=None):
    """ (circuits, groundset=None)

        circuits __ set of circuits of a matroid

        groundset __ optionally a groundset for the matroid,
                     most useful if there are coloops

        returns a BasisMatroid that corresponds to the circuits given
    """
    circuits = setFamilize(circuits)
    if groundset is None:
        groundset = uniteAll(circuits)
    groundset = frozenset(groundset)
    current_bases = set([groundset])
    for c in circuits:
        new_bases = set()
        for b in current_bases:
            if c.issubset(b):
                for x in c:
                    new_bases.add(b.difference([x]))
            else:
                new_bases.add(b)
        current_bases = new_bases
    rank = max((len(b) for b in current_bases))
    return BasisMatroid(bases=[b for b in current_bases if len(b)==rank],groundset=groundset)

def getSignedCocircuits(C, groundset=None):
    """ (C, groundset=None)

        C __ family of signed circuits of an oriented matroid

        groundset __ optionally give groundset of oriented matroid,
                     useful for coloops

        return C*, the signed cocircuits of the oriented matroid given by C
    """
    # cocircuits are the complements of hyperplanes, but IDK how this could help here
    circuits = set(frozenset((a for a,s in c0)) for c0 in C)
    M = CircuitBasisMatroid(circuits,groundset=groundset)
    D = set()
    for d in M.dual().circuits():
        d0 = list(d)[0]
        if len(d) < 2:
            D.add(frozenset([(d0,1)]))
            D.add(frozenset([(d0,-1)]))
            continue
        C0 = [c for c in C if len(d.intersection((a for a,s in c)))==2 and (d0,1) in c]
        # Confused? Look up Lemma 2.2.3 in Bland & Las Vergnas "Orientability of Matroids" 1978
        dplus = set([(d0,1)])
        dminus = set([(d0,-1)])
        for c0 in C0:
            elem,sign = [(a,s) for a,s in c0 if (a in d) and (a != d0)][0]
            dplus.add((elem,-sign))
            dminus.add((elem,sign))
        D.add(frozenset(dplus))
        D.add(frozenset(dminus))
    return D


def signedSubsetsToIntegerLattice(C):
    """ (C)

        C __ set of signed subsets

        returns I,S
                where
                I __ corresponding integer lattice
                S __ support order
                L __ list of all generators (redundant)
    """
    support = sorted(set([x for x,s in uniteAll(C)]))
    L = [tuple((1 if (support[i],+1) in c0 else (-1 if (support[i],-1) in c0 else 0)
            for i in range(len(support)))) for c0 in C]
    return IntegerLattice(L), support, L


def signedSubsetOrthogonal(C,D):
    """ (C,D)

        C,D __ signed subsets

        returns true, if C and D are orthogonal.
    """
    positive = False
    negative = False
    for (c,s) in C:
        if (c,s) in D:
            positive = True
        elif (c,-s) in D:
            negative = True
        if positive and negative:
            return True
    return positive == negative

def dependentNonTrivialModularPairsOfFlats(M):
    """ (M)

        M __ matroid

        returns a generator for all modular pairs of flats that have at least one dependent
            component, and that are incomparable with respect to subset-order.
    """
    return ((A,B) for A,B in allModularPairsOfFlats(M) if M.is_dependent(A.union(B))
    and (not (A.issubset(B) or B.issubset(A)) ))

def getFlatDifference(M1,M2, dependentOnly=False):
    """ (M1, M2, dependentOnly=False)

        M1, M2 __ matroids

        dependentOnly __ if True, only return dependent flats.

        returns the flats of M1, that are not flats of M2
    """
    G2 = M2.groundset()
    return (F for F in allFlats(M1) if((not dependentOnly) or M1.is_dependent(F))
     and  ( (not F.issubset(G2)) or (not M2.is_closed(F))))

# RECENT ADDITIONS

#
# Slightly modified version of _has_minor from matroid.pyx from sage 8.0
#

cpdef hasMinorWith(self, N, E0, bint certificate=False):
    """
    (M, N, E0, bint certificate=False)
    Test if matroid M has the specified minor, that contains the set E0
    and optionally return frozensets ``X`` and ``Y`` so that ``N`` is isomorphic to ``self.minor(X, Y)``.

    INPUT:

    - ``N`` -- An instance of a ``Matroid`` object,
    - ``certificate`` -- Boolean (Defalt: ``False``) If ``True``, returns
      ``True, (X, Y, dic) where ``N`` is isomorphic to ``self.minor(X, Y)``,
      and ``dic`` is an isomorphism between ``N`` and ``self.minor(X, Y)``.

    OUTPUT:

    boolean or tuple.

    EXAMPLES::

        sage: M = matroids.named_matroids.Vamos()
        sage: M._has_minor(matroids.Whirl(3))
        False
        sage: M._has_minor(matroids.Uniform(2, 4))
        True
        sage: M._has_minor(matroids.Uniform(2, 4), certificate=True)
        (True, (frozenset({'a', 'c'}), frozenset({'b', 'e'}),
            {0: 'h', 1: 'd', 2: 'g', 3: 'f'}))

    .. TODO::

        This important method can (and should) be optimized considerably.
        See [Hli2006]_ p.1219 for hints to that end.
    """
    if self is N:
        if certificate:
           return True, (frozenset(), frozenset(), {x: x for x in self.groundset()})
        return True
    rd = self.full_rank() - N.full_rank()
    cd = self.full_corank() - N.full_corank()
    if rd < 0 or cd < 0:
        if certificate:
            return False, None
        return False
    YY = []
    for Y in self.dual().independent_r_sets(cd):
        if not Y.intersection(E0):
            YY.append(Y)
    for X in self.independent_r_sets(rd):
        if X.intersection(E0):
            continue
        for Y in YY:
            if X.isdisjoint(Y):
                if N._is_isomorphic(self._minor(contractions=X, deletions=Y)):
                    if certificate:
                        return True, (X, Y, N._isomorphism(self._minor(contractions=X, deletions=Y)))
                    return True
    if certificate:
        return False, None
    return False

def vertexBound(n,r):
    if r <= 3: # either strict gammoid or no gammoid
        return n
    if r >= n-3: # either transversal matroid or no gammoid
        return n + r
    return r*r*n + r + n

def arcBoundStrict(n,r):
    return (n-r)*(n-1) # Mason '72 Corollary 2.5

def augmentList(L,n):
    L = list(L)
    i = int(1)
    for j in range(n):
        while i in L:
            i += 1
        L.append(i)
    return L

class NonLoopArcIterator:
    def __init__(self, V):
        self.V = list(V)
        self.lenV = len(self.V)
        self.x = 0
        self.y = 0
    def move2(self, x,y):
        self.x = x
        self.y = y
    def next(self):
        if self.x < self.y-1:
            self.x += 1
        elif self.x == self.y -1:
            self.x = self.y
            self.y = 0
        elif self.y < self.x-1:
            self.y += 1
        else: # y == x-1 or y == x
            if self.lenV <= self.x+1:
                raise StopIteration
            self.y = self.x+1
            self.x = 0
        return (self.V[self.x], self.V[self.y])
    def done(self):
        if self.x < self.y-1:
            return False
        elif self.x == self.y -1:
            return False
        elif self.y < self.x-1:
            return False
        else: # y == x-1 or y == x
            if self.lenV <= self.x+1:
                return True
            return False

def vertexBound2(n,r):
#    if r <= 3: # either strict gammoid or no gammoid
#        return n
#    if r >= n-3: # either transversal matroid or no gammoid
#        return n + r
    return r*r*n + r + n

def arcMinimalGammoidStdReprB(M, T=None, vertexLimit=None, arcLimit=None):
    """ (M, T=None, vertexLimit=None, arcLimit=None)

        M __ matroid
        T __ (optional) sink set (use any base of M)

        find a standard representation with the sink set T that has a
           minimal cardinality arc set.
    """
    if T is None:
        T = frozenset(M.bases()[0])
    else:
        if len(T) != M.rank() or (not M.is_independent(T)):
            raise "Target set is invalid!"
    BM = frozenset(M.bases())
    EBM = frozenset((M.groundset().difference(B) for B in BM))
    if vertexLimit is None:
        vertexLimit = vertexBound2(len(M.groundset()),M.rank())
    if arcLimit is None:
        arcLimit = arcBoundStrict(vertexLimit,M.rank())
    V = sorted(T) + sorted(M.groundset().difference(T))
    E = frozenset(V)
    ET = E.difference(T)
    if len(V) > vertexLimit:
        return False
    if len(V) < vertexLimit:
        V = augmentList(V,vertexLimit - len(V))
    sink_routing = frozenset([(t,t,frozenset([t])) for t in T])
    essentialMaximalRoutings = set([( T,sink_routing, T )])
    newEssentialMaximalRoutings = []
    rollbackIndex = [int(-1)]
    noLongerEssentialMaximalRoutings = []
    rollbackIndex1 = [0]
    independentBases = [T]
    rollbackIndex2 = [0]
    newEssentialPaths = []
    rollbackIndex3 = [0]
    noLongerEssentialPaths = []
    rollbackIndex4 = [0]
    rollbackArc = [None]
    rollbackArcIdx = [(0,0)]
    rollbackVmax = [int(0)]
    requestRollback = False
    nbrOfBases = len(M.bases())
    arcCount = int(0)
    D = DiGraph()
    D.add_vertices(V)
    arcs = NonLoopArcIterator(V)
    essentialPaths = {}
    for u in V:
        for v in V:
            essentialPaths[(u,v)] = set()
    for v in V:
        essentialPaths[(v,v)] = set([frozenset([v])])
    result = False
    Vmax = int(len(E))
    print "T=",sorted(T)
    while 1:
        if len(independentBases) == nbrOfBases and not requestRollback:
            print "Best representation: ",arcCount,"arcs"
            print "   ", ",".join(map(lambda x: str(x[0])+ "->"+ str(x[1]), D.edges()))
            result = copy(D), T, sorted(M.groundset()) # ''return 1''
            arcLimit = arcCount - 1
        if arcs.done() or arcCount >= arcLimit or requestRollback:
            # pop state from stack
            idx = rollbackIndex.pop()
            idx1 = rollbackIndex1.pop()
            idx2 = rollbackIndex2.pop()
            idx3 = rollbackIndex3.pop()
            idx4 = rollbackIndex4.pop()
            arc = rollbackArc.pop()
            Vmax = rollbackVmax.pop()
            arcx,arcy = rollbackArcIdx.pop()
            if idx < int(0): # ''d = 0''
                return result
            essentialMaximalRoutings.difference_update(
                newEssentialMaximalRoutings[idx:])
            essentialMaximalRoutings.update(
                noLongerEssentialMaximalRoutings[idx1:])
            del newEssentialMaximalRoutings[idx:]
            del noLongerEssentialMaximalRoutings[idx1:]
            del independentBases[idx2:]
            for v,w,p in newEssentialPaths[idx3:]:
                essentialPaths[(v,w)].discard(p)
            for v,w,p in noLongerEssentialPaths[idx4:]:
                essentialPaths[(v,w)].add(p)
            del newEssentialPaths[idx3:]
            del noLongerEssentialPaths[idx4:]
            arcCount -= int(1)
            D.delete_edge(arc[0],arc[1])
            arcs.move2(arcx,arcy)
            requestRollback = False
        else:
            arc = arcs.next()
            if arc[0] in T: # skip arcs with sink-tails
                continue
            if arc[1] in ET:
                continue
            #maxV = max(arcs.x,arcs.y)
            #if  maxV >= idxVmax: #adjust for new arc limit
            #    requestRollback = True
            #    continue
            if arcs.y > Vmax: #against time waste with huge vertex spaces
                requestRollback = True
                continue
            # push state to stack
            rollbackArc.append(arc)
            rollbackArcIdx.append((arcs.x,arcs.y))
            rollbackIndex.append(int(len(newEssentialMaximalRoutings)))
            rollbackIndex1.append(int(len(noLongerEssentialMaximalRoutings)))
            rollbackIndex2.append(int(len(independentBases)))
            rollbackIndex3.append(int(len(newEssentialPaths)))
            rollbackIndex4.append(int(len(noLongerEssentialPaths)))
            rollbackVmax.append(Vmax)
            # update digraph
            if arcs.y == Vmax:
                Vmax += int(1)
            left_part = []
            right_part = []
            for v in V:
                for p in essentialPaths[(v,arc[0])]:
                    left_part.append( (v, p) )
                for p in essentialPaths[(arc[1],v)]:
                    right_part.append( (v, p) )
            new_paths = set()
            for l0,l in left_part:
                for r0,r in right_part:
                    if l.intersection(r):
                        continue
                    non_essential_path = False
                    for x in l:
                        for y in r:
                            if D.has_edge(x,y):
                                non_essential_path = True
                                break
                        if non_essential_path:
                            break
                    if non_essential_path:
                        continue
                    p = l.union(r)
                    new_paths.add((l0,r0,p))
            idx4 = len(noLongerEssentialPaths)
            for v,w,p in new_paths:
                superseeded = []
                for q in essentialPaths[(v,w)]:
                    if p.issubset(q):
                        superseeded.append(q)
                        noLongerEssentialPaths.append((v,w,q))
                newEssentialPaths.append((v,w,p))
                essentialPaths[(v,w)].difference_update(superseeded)
                essentialPaths[(v,w)].add(p)
            criterion = [x for x in noLongerEssentialPaths[idx4:]
                                      if x[0] in E and x[1] in T]
            idx = len(newEssentialMaximalRoutings)
            idx1 = len(noLongerEssentialMaximalRoutings)
            new_E_paths = [x for x in new_paths if x[1]in T and x[0]in E]
            for X,R,P in essentialMaximalRoutings:
                if R.intersection(criterion):
                    noLongerEssentialMaximalRoutings.append((X,R,P))
                else:
                    for v,w,p in new_E_paths:
                        if not w in X:
                            continue
                        if len(p.intersection(P)) > 1:
                            continue
                        X1 = X.difference([w]).union([v])
                        if not X1 in independentBases:
                            if not X1 in BM:
                                # found excess base
                                requestRollback = True
                                break
                            independentBases.append(X1)
                        R1 = R.difference([(w,w,frozenset([w]))]).union(
                                                              [(v,w,p)])
                        if R1.intersection(sink_routing):
                            newEssentialMaximalRoutings.append(
                                (X1,R1,P.union(p)))
                    if requestRollback:
                        break
            essentialMaximalRoutings.difference_update(
                noLongerEssentialMaximalRoutings[idx1:])
            essentialMaximalRoutings.update(
                newEssentialMaximalRoutings[idx:])
            D.add_edge(arc[0],arc[1])
            arcCount += int(1)


def toSignedSubset(s):
    """ (s)

        s __ comma separated element list

        returns a signed subset dictionary for s
    """
    C = {}
    for x in s.split(","):
        x = x.strip()
        if x.startswith("-"):
            x = x[1:].strip()
            C[x] = -1
        else:
            C[x] = 1
    return C

def reverseLexicographicTuples(E,r):
    """ (E,r)

        E __ groundset
        r __ rank
    """
    list0 = [tuple(reversed(Y)) for Y in sorted((list(reversed(sorted(X))) for X in itertools.combinations(E,r)))]
    return list0

def lexicographicTuples(E,r):
    """ (E,r)

        E __ groundset
        r __ rank
    """
    return sorted(itertools.combinations(E,r))

### ---- ###

def getChiSign(X, finschi_vector="+++++++++++++-++--++", orderedE=None):
    """ (X, finschi_vector="+++++++++++++-++--++", orderedE=None)

        X __ subset of {1,2,...,n} of rank cardinality for which the sign is desired

        returns the sign of chi(X) of the matroid given by a vector from Lukas Finschi's O.M. db.
    """
    I,s = getFinschiIndexAndSign(X, orderedE)
    if finschi_vector[I] == "+":
        return s
    elif finschi_vector[I] == "-":
        return -s
    return 0

def getFixedPattern(M):
    """ (M)

        M __ matroid.

        returns a pattern that corresponds to Finschi-DB orientations of M
    """
    g = list(M.groundset())
    r = M.rank()
    Ts = reverseLexicographicTuples(range(len(g)),r)
    chi = [0 if M.is_dependent([g[x] for x in X]) else 1 for X in Ts]
    for s in Permutations(len(g)):
        chi2 = [0 if M.is_dependent([g[s[x]-1] for x in X]) else 1 for X in Ts]
        if chi > chi2:
            chi = chi2
    return chi

def getGrepPattern(M):
    """ (M)

        M __ matroid

        returns a string that can be used to grep orientations of M from
        L. Finschi's dbomview output"""
    pat = ["[+-]" if x == 1 else "0" for x in getFixedPattern(M)]
    return "grep '" + "".join(pat) + "'"

def getMatroidAutomorphismGroup(M):
    """ (M)

        M __ matroid

        returns the automorphism group of M
    """
    IS = IncidenceStructure(M.bases())
    return IS.automorphism_group()


def getFinschiIndexAndSign(X ,orderedE=None):
    """ (X ,orderedE=None)

        X __ subset of {1,2,...,N} of correct cardinality,
             for which the corresponding index of the Finschi chirotope string
             is desired

        returns (I,s) where
            I is the column index for looking up a particular tuple of elements of E,
            and s is the permutation sign (+1) or (-1).
        """
    if orderedE is None:
        orderedE = [(i+1) for i in range(max(X))]
    R = [orderedE.index(x)+1 for x in X]
    Rs = sorted(R)
    try:
        s = Permutation([Rs.index(r)+1 for r in R])
    except ValueError:
        # in this case, we have that some element of the groundset occurs twice,
        # therefore the Grassman-Plücker-Identity makes chi(X)=0, since
        # we have to evaluate the determinant of a matrix with dependent columns
        return (0,0) # safe return value for vectors with double occurrences
    I = 0
    for (x,i) in zip(Rs,range(1,1+len(R))):
        I += binomial(x-1,i)
    return I,s.sign()


### ---- ###


def isReorientation(C,D):
    """ (C,D)

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
    """
    needInversion = set()
    needSame = set()
    C0 = {}
    for c in C:
        c0 = frozenset((x for x,s in c))
        C0[c0] = C0.get(c0,[])+[c]
    reasons = {}
    for d in D:
        d0 = frozenset((x for x,s in d))
        if not d0 in C0: #no circuit in C0 has the same support as d
            return False, [d]
        fixed = needInversion.union(needSame).intersection(d0)
        foundSolution = False
        for c in C0[d0]:
            negative = [x for x,i in d if (x,-i) in c]
            positive = [x for x,i in d if (x,i) in c]
            if needInversion.intersection(positive) or needSame.intersection(negative):
                continue
            foundSolution = True
            break
        if not foundSolution:
            return False, sorted(set([reasons[x] for x in d0.intersection(needInversion.union(needSame))])) + [d], sorted(needInversion)
        else:
            for x in positive:
                if not x in needSame:
                    reasons[x] = d
                    needSame.add(x)
            for x in negative:
                if not x in needInversion:
                    reasons[x] = d
                    needInversion.add(x)

    return True, [], sorted(needInversion)

def relabelSignedSets(C, sigma):
    """ (C,sigma)

        C __ family of signed subsets
        sigma __ relabelling permutation, i.e.
                we call sigma(x)

        returns C, where every subset is relabelled by sigma
    """
    return [frozenset(((sigma(x),s) for x,s in c)) for c in C]

### ---- ###


def printSignedCircuitsLatex(C, perRow=[3], filterNegative=True, phantomMinus=[False]):
    count = 0
    first = True
    print r"\begin{align*}"
    if filterNegative:
        print r" \Ccal = \pm \{ & "
    else:
        print r" \Ccal = \{ & "

    def myCmp(x,y):
        c = cmp(len(x),len(y))
        if c == 0:
            c = cmp(sorted(x),sorted(y))
        return c
    for c in sorted(C,myCmp):
        mc = frozenset((x,-i) for x,i in c)
        if filterNegative:
            if len([i for x,i in c if i < 0]) > len([i for x,i in c if i > 0]):
                continue
            if len([i for x,i in c if i < 0]) == len([i for x,i in c if i > 0]) \
               and (sorted(c) < sorted(mc)):
               continue


        if not first:
            print ", "
        if not first and count%(perRow[0]) == 0:
            print " \\\\ & "
            if len(perRow) > 1:
                perRow = perRow[1:]
                count = 0
            if len(phantomMinus) > 1:
                phantomMinus = phantomMinus[1:]
        count += 1
        first = False
        print "\\SET{",
        comma = 0

        for e,s in sorted(c):
            if comma:
                print ",",
            if s > 0:
                if phantomMinus[0]:
                    print "\\hphantom{-}",e,
                else:
                    print e,
            else:
                print "-",e,
            comma = 1

        print "}",
    print r"\}"
    print r"\end{align*}"


def powerset(s):
    """ (s)

        return a chain-iterator for the powerset of s """
    return chain.from_iterable(combinations(s, r) for r in xrange(len(s)+1))

def powersetSubsetIndex(S, X):
    """ (S, X)

        S __ subset of X
        X __ universe (list or implicitly sorted)

        returns the iteration index where the subset S occurs in the powerset
        iterator
    """
    if type(X) != list:
        X = sorted(X)
    idx0 = 0
    for i in range(len(S)):
        idx0 += binomial(len(X),i)
    idx00 = idx0
    idxs = sorted((X.index(s) for s in S))
    x0 = 0
    s0 = 0
    for i in idxs:
        for j in range(x0,i):
            # add number of choices where j is fixed at position s0;
            # consequently, the subsequent numbers must be bigger than j.
            idx0 += binomial(len(X) - j -1, len(S) - s0 - 1)
        s0 += 1
        x0 = i + 1
    return idx0

### ---- ###


def allFlats(M):
    """ (M)

        return a chain-iterator of all flats of M, with ascending rank """
    return chain.from_iterable(M.flats(r) for r in xrange(0,M.rank()+1))

def leqWrtFlats(l,r,flats):
    """ (l,r, flats)

        l,r __ operands

        flats __ set/family of frozensets

        compares whether l is a subset of r, and if l is a proper subset,
                whether l in flats;
                returns True if l <=(flats) r.
    """
    l = frozenset(l)
    r = frozenset(r)
    if l == r:
        return True
    if not l.issubset(r):
        return False
    if not l in flats:
        return False
    return True

def downsetWrtFlats(r,flats):
    """ (r,flats)

       r __ operand

       flats __ set/family of frozensets

       returns the subsets l of r, for which l <=(flats) r holds.
    """
    r = frozenset(r)
    return frozenset([r] + [l for l in flats if l.issubset(r)])


def alphaPosetLeq(M):
    """ (M)

        M __ matroid

        returns a function that compares whether l <= r with respect to
                the alpha_M poset, and then returns either True of False
    """
    return lambda l,r,f=frozenset(allFlats(M)): leqWrtFlats(l,r,f)

def alphaPosetDownsets(M):
    """ (M)

        M __ matroid

        returns a function that gives the downsets of the alpha_M poset
    """
    return lambda r,f=frozenset(allFlats(M)): downsetWrtFlats(r,f)


def moebiusMatrixForAlphaPoset(M):
    """ (M)

        M __ matroid

        returns the Moebius-function of the alpha_M poset.
    """
    G = sorted(M.groundset())
    nG = len(G)
    mu = Matrix(2**nG,2**nG,sparse=True)
    idx1 = -1
    leq = alphaPosetLeq(M)
    downset = alphaPosetDownsets(M)
    for L in powerset(G):
        idx1 += 1
        idx2 = -1
        for R in powerset(G):
            idx2 += 1
            if L == R:
                mu[idx1,idx2] = 1
            elif leq(L,R):
                s = 0
                for P in downset(R):
                    if P == R:
                        continue
                    s += mu[idx1,powersetSubsetIndex(P,G)]
                mu[idx1,idx2] = -s
    return mu

def alphaVector(M):
    """ (M)

        M __ matroid

        returns the alpha vector of M
    """

    G = sorted(M.groundset())
    nG = len(G)
    alpha = Matrix(1,2**nG,sparse=True)
    idx1 = -1
    leq = alphaPosetLeq(M)
    downset = alphaPosetDownsets(M)
    for L in powerset(G):
        idx1 += 1
        aval = len(L) - M.rank(L)
        for R in downset(L):
            if R == L:
                continue
            aval -= alpha[0,powersetSubsetIndex(R,G)]
        if aval:
            alpha[0,idx1] = aval
    return alpha

def calculateAlphaOfExtension(e, C, M, alpha=None, mu=None):
    """ (e, C, M, alpha=None, mu=None)


            e __ name of the new element
            C __ modular cut of the new element (whole cut, not just minimal elts!)
            M __ matroid

            alpha __ alpha vector of M
            mu  __ Möbius function of the alpha_M-poset

        returns the alpha vector of M+e that corresponds to C
    """
    G0 = sorted(M.groundset())
    G1 = sorted(G0+[e])
    if alpha is None:
        alpha = alphaVector(M)
    if mu is None:
        mu = moebiusMatrixForAlphaPoset(M)

    alphaE = Matrix(1,2**len(G1),sparse=True)
    idxE = -1
    deltaAlphaE = {}

    for X in powerset(G1):
        X = frozenset(X)
        idxE += 1
        val = 0
        if e in X:
            X0 = X.difference([e])
            clX0 = M.closure(X0)
            if not clX0 in C:
                if clX0 == X0:
                    val = 0
                else:
                    val = alpha[0,powersetSubsetIndex(X0,G0)]
            else:
                d = 1
                for Z in C:
                    if Z.issubset(X0):
                        if Z == X0:
                            continue
                        #print setStr(Z), "<=", setStr(X0)
                        d -= deltaAlphaE[Z]
                deltaAlphaE[X0] = d
                val = alpha[0,powersetSubsetIndex(X0,G0)] + d
        else:
            s = 0
            for Y in powerset(X):
                Y = frozenset(Y)
                if Y == X:
                    continue
                nuY = len(Y) - M.rank(Y)
                for Z in C:
                    Z = frozenset(Z)
                    if not Y.issubset(Z):
                        continue
                    if not Z.issubset(X):
                        continue
                    if Z == X:
                        continue
                    s += nuY * mu[powersetSubsetIndex(Y,G0),powersetSubsetIndex(Z,G0)]
            val = alpha[0,powersetSubsetIndex(X,G0)] + s # Lemma 2.4.16
        if val:
            alphaE[0,idxE] = val
    return alphaE

def getAllModularCuts(M):
    """ (M)

        M __ matroid

        returns all modular cuts of M, except the empty modular cut.
        (SAGE does not allow an extension with a coloop through M.extension !!)
    """
    H = frozenset(M.hyperplanes())
    L = [frozenset(l) for l in M.linear_subclasses()]
    Ms = [set() for l in L]
    for F in allFlats(M):
        for m,l in zip(Ms,L):
            contained = True
            for h in H:
                if F.issubset(h):
                    if not h in l:
                        contained = False
                        break
            if contained:
                m.add(F)

    return tuple(( frozenset(x) for x in Ms ))



def canonicalMatroidLabel(M):
    """ (M)

        M __ matroid

        returns the canonical label of the matroid M;
               which is a tuple
    """
    IS = IncidenceStructure(M.bases())
    phi = IS.canonical_label()

    return (frozenset((frozenset((phi[x] for x in B)) for B in M.bases())), len(M.groundset()))

### ---- ###




def isGammoid(M, vertexLimit=None, arcLimit=None):
    """ (M, vertexLimit=None, arcLimit=None)

        M __ matroid

        vertexLimit __ max. number of vertices allowed in representation
        arcLimit    __ max. number of arcs allowed in representation

        returns either False if M is not a gammoid (with restrictions),
                or a representation triple (D,T,E)
                        D __ digraph
                        T __ target nodes
                        E __ ground set
    """
    T = M.bases()[0]
    if vertexLimit is None:
        vertexLimit = vertexBound(len(M.groundset()),M.rank())
    if arcLimit is None:
        arcLimit = arcBoundStrict(vertexLimit,M.rank())
    V = sorted(T) + sorted(M.groundset().difference(T))
    if len(V) > vertexLimit:
        return False
    if len(V) < vertexLimit:
        V = augmentList(V,vertexLimit - len(V))
    #initialize stack
    essentialMaximalRoutings = set([( frozenset(T),frozenset([(t,t,frozenset([t])) for t in T]), frozenset(T) )])
    newEssentialMaximalRoutings = []
    rollbackIndex = [-1]
    noLongerEssentialMaximalRoutings = []
    rollbackIndex1 = [0]
    independentBases = [T]
    rollbackIndex2 = [0]
    newEssentialPaths = []
    rollbackIndex3 = [0]
    noLongerEssentialPaths = []
    rollbackIndex4 = [0]
    rollbackArc = [None]
    requestRollback = False
    #initialize counts, and keep track of the digraphs structure
    nbrOfBases = len(M.bases())
    arcCount = 0
    D = DiGraph()
    D.add_vertices(V)
    arcs = NonLoopArcIterator(V)
    essentialPaths = {}
    for u in V:
        for v in V:
            essentialPaths[(u,v)] = set()
    for v in V:
        essentialPaths[(v,v)] = set([frozenset([v])])
    #print "Target set:",sorted(T)
    while 1:
        #print "Head - Edges: ", sorted((u,v) for u,v,lbl in D.edges())
        #print "Essential Paths:"
        #for u,v in essentialPaths:
        #    for p in essentialPaths[(u,v)]:
        #        print "   ",u,"to",v,"via",sorted(p)
        if len(independentBases) == nbrOfBases and not requestRollback:
            #every base is independent and there is no additional indepenent set
            return D, T, sorted(M.groundset())
        if arcs.done() or arcCount >= arcLimit or requestRollback:
            #if arcCount == arcLimit:
            #    print "At arc count limit."
            #if requestRollback:
            #    print "Rollback requested."
            #if arcs.done():
            #    print "No more arcs."
            #rollback
            idx = rollbackIndex.pop()
            idx1 = rollbackIndex1.pop()
            idx2 = rollbackIndex2.pop()
            idx3 = rollbackIndex3.pop()
            idx4 = rollbackIndex4.pop()
            arc = rollbackArc.pop()
            #print "removing: ",arc," idxs:", idx, idx1, idx2, idx3, idx4
            if idx < 0:
                #exhausted all possibilities
                return False
            essentialMaximalRoutings = essentialMaximalRoutings.difference(newEssentialMaximalRoutings[idx:]).union(noLongerEssentialMaximalRoutings[idx1:])
            newEssentialMaximalRoutings = newEssentialMaximalRoutings[:idx]
            noLongerEssentialMaximalRoutings = noLongerEssentialMaximalRoutings[:idx1]
            independentBases = independentBases[:idx2]
            for v,w,p in newEssentialPaths[idx3:]:
                #print "removing", v,'to',w,'via',sorted(p)
                essentialPaths[(v,w)] = essentialPaths[(v,w)].difference([p])
                #print "Routes left:",[sorted(x) for x in essentialPaths[(v,w)]]
            for v,w,p in noLongerEssentialPaths[idx4:]:
                essentialPaths[(v,w)] = essentialPaths[(v,w)].union([p])
            newEssentialPaths = newEssentialPaths[:idx3]
            noLongerEssentialPaths = noLongerEssentialPaths[:idx4]
            arcCount -= 1
            D.delete_edge(arc[0],arc[1])
            arcs.move(arc)
            requestRollback = False

        else:
            #add an arc
            arc = arcs.next()
            if arc[0] in T:
                #print "Skipping sink arc:", arc
                continue
            #else:
                #print "Adding:", arc
            rollbackArc.append(arc)
            rollbackIndex.append(len(newEssentialMaximalRoutings))
            rollbackIndex1.append(len(noLongerEssentialMaximalRoutings))
            rollbackIndex2.append(len(independentBases))
            rollbackIndex3.append(len(newEssentialPaths))
            rollbackIndex4.append(len(noLongerEssentialPaths))
            left_part = set()
            right_part = set()
            for v in V:
                for p in essentialPaths[(v,arc[0])]:
                    left_part.add( (v, p) )
                for p in essentialPaths[(arc[1],v)]:
                    right_part.add( (v, p) )
            new_paths = set()
            for l0,l in left_part:
                for r0,r in right_part:
                    if l.intersection(r):
                        continue
                    non_essential_path = False
                    for x in l:
                        for y in r:
                            if D.has_edge(x,y):
                                non_essential_path = True
                                break
                        if non_essential_path:
                            break
                    if non_essential_path:
                        continue
                    p = l.union(r)
                    new_paths.add((l0,r0,p))
            idx4 = len(noLongerEssentialPaths)
            for v,w,p in new_paths:
                superseeded = []
                for q in essentialPaths[(v,w)]:
                    if p.issubset(q):
                        superseeded.append(q)
                        noLongerEssentialPaths.append((v,w,q))
                newEssentialPaths.append((v,w,p))
                essentialPaths[(v,w)] = essentialPaths[(v,w)].difference(superseeded).union([p])
            criterion = set(noLongerEssentialPaths[idx4:])
            idx = len(newEssentialMaximalRoutings)
            idx1 = len(noLongerEssentialMaximalRoutings)
            for X,R,P in essentialMaximalRoutings:
                if R.intersection(criterion):
                    noLongerEssentialMaximalRoutings.append((X,R,P))
                else:
                    for v,w,p in new_paths:
                        if not w in X:
                            continue
                        if not (p.intersection(P)).issubset([w]):
                            continue
                        #print "old essential routing:", sorted(X)
                        #for px in R:
                        #    print " ... path ",px[0], " to ",px[1], "via",sorted(px[2])
                        #print "essential new path:", v ,"to", w, "via",sorted(p)

                        X1 = X.difference([w]).union([v])
                        if not M.is_independent(X1.intersection(M.groundset())):
                            requestRollback = True
                            #print sorted(X1.intersection(M.groundset())), " should not be independent -> Rollback"
                            break
                        if X1.issubset(M.groundset()):
                            if not X1 in independentBases:
                                independentBases.append(X1)
                                #print "New independent base:", sorted(X1)
                        P1 = P.union(p)
                        R1 = set()
                        for x,y,p1 in R:
                            if x == w:
                                R1.add((v,y,p1.union(p)))
                            else:
                                R1.add((x,y,p1))
                        R1 = frozenset(R1)
                        newEssentialMaximalRoutings.append((X1,R1,P1))
                    if requestRollback:
                        break
            essentialMaximalRoutings = essentialMaximalRoutings.difference(noLongerEssentialMaximalRoutings[idx1:]).union(newEssentialMaximalRoutings[idx:])
            D.add_edge(arc[0],arc[1])
            arcCount += 1
### ---- ###


def computeArcMinRepresentationOfUniformMatroid(n,r):
    """ (n,r)

        n __ number of elements
        r __ rank

        returns an arc-minimal representation of the uniform matroid U(n,r)
                as a gammoid.
    """
    if r > n:
        r = n
    print "Searching Arc-Minimal Representation of U(%d,%d)"%(n,r)
    E = list(range(1,n+1))
    D = DiGraph()
    T = list(range(1,r+1))
    for e in range(r+1,n+1):
        for t in T:
            D.add_edge(e,t)
    best_bound = (n-r)*r
    U = BasisMatroid(groundset=E, bases=list(combinations(E,r)))
    print "|A|=",best_bound
    while 1:
        better_arcs = best_bound - 1
        better_vertices = 2*better_arcs
        print "Testing |V| <= %d and |A| <= %d"%(better_vertices,better_arcs)
        X = isGammoid(U,better_vertices,better_arcs)
        if X == False:
            print "  ... bound cannot be satisfied"
            break
        else:
            D,T,E = X
            best_bound = len(D.edges())
            print "|A|=",best_bound

    print "|A|=",best_bound
    return D,T,E

### ---- ###


def arcBoundStrict(n,r):
    """ (n,r)

        n __ number of elements in the ground set
        r __ rank

        returns the upper bound for the number of arcs needed
        to represent a *strict* gammoid with n elements of rank r
    """
    # Mason '72: Corollary 2.5  sum alpha(F)*(|F|-1) is an upper bound for
    # the number of arcs needed to represent M
    # ... alpha(F) adds up to the nullity
    # (|F|-1) is at most |E|-1
    return (n-r)*(n-1)

### ---- ###


def FreeMatroid(E):
    """ (E)
        E __ groundset

        returns the free matroid on E
    """
    return BasisMatroid(bases=[list(E)],groundset=list(E))

def UniformMatroid(E,r):
    """ (E)
        E __ groundset
        r __ rank

        return the uniform matroid U(E,r)
    """
    E = list(E)
    return BasisMatroid(bases=list(combinations(E,r)),groundset=E)

def DirectSumMatroid(M,N):
    """ (M,N)
        M,N __ matroids

        returns the direct sum of M and N
    """
    E0 = [(e,0) for e in M.groundset()] + [(e,1) for e in N.groundset()]
    B0 = [[(x,0) for x in X]+[(y,1) for y in Y] for X in M.bases() for Y in N.bases()]
    return BasisMatroid(bases=B0,groundset=E0)


### ---- ###


class AlphaMatroid(object):
    def __init__(self, M):
        """ (M)
            M __ matroid

            creates a decorated matroid object with added functionality for
               gammoid and strict gammoid backtracking
        """
        self.M = M
        self.E = tuple(sorted(M.groundset()))
        self._alpha = None
        self.history = ""
        self.dualized = None
        self._V = None
        self._VD = None
        self._VC = None
        self._VDC = None
        self._situation_label = None
        self._modcuts = None
        self._nontrivialmodcuts = None
        self._mu = None
        for name in set(dir(M))-set(dir(self)):
            setattr(self, name, getattr(M,name))

    def __cmp__(self,R):
        if type(R) is AlphaMatroid:
            return cmp(self.M,R.M)
        else:
            return cmp(self.M,R)

    def modular_cuts(self):
        """ ()

            returns a tuple of all modular cuts of this matroid
        """
        if self._modcuts is None:
            self._modcuts = getAllModularCuts(self.M)
        return self._modcuts

    def non_principal_modular_cuts(self):
        """ ()

            returns a tuple of all non-principal modular cuts of this matroid
        """
        if self._nontrivialmodcuts is None:
            self._nontrivialmodcuts = tuple((C for C in self.modular_cuts() if len(getMinimalFamily(C)) > 1))
        return self._nontrivialmodcuts


    def alpha(self):
        """ ()

            returns the alpha vector of M, which is sorted in the power-set
                    enumeration order of powerset(self.E)
        """
        if self._alpha is None:
            self._alpha = alphaVector(self.M)
        return self._alpha

    def mu(self):
        """ ()

            returns the Moebius-function of the alpha_M poset of this matroid.
        """
        if self._mu is None:
            self._mu = moebiusMatrixForAlphaPoset(self)
        return self._mu

    def is_strict_gammoid(self):
        """ ()

            returns True, if M is a strict gammoid
        """
        return min(self.alpha()[0]) >= 0

    def V(self):
        """ ()

            returns a dictionary D, where each key is a violation X in V(M);
            and the value is a dictionary that
            corresponds to the alpha summation at X.
        """
        if self._V is None:
            self._V = findViolations(self)
        return self._V

    def is_similar(self,AM, certificate=False):
        """ (AM, certify=False)

            AM __ other matroid

            returns the test whether M.VDC() is isomorphic to AM.VDC()
        """
        AM = decorateAlphaMatroid(AM)
        return self.VDC().is_isomorphic(AM.VDC(),edge_labels=True,certificate=certificate)

    def situation_label(self):
        """ ()

            returns an immutable digraph that is the canonical_label of VDC()
        """
        if self._situation_label is None:
            self._situation_label = self.VDC().canonical_label().copy(immutable=True)
        return self._situation_label

    def VC(self):
        """ ()

            returns a dictionary D, where each key corresponds to a violation X
            in V(M);
            and each value corresponds to the modular cuts in M restricted to
            the non-zero alpha summands for X
        """
        if self._VC is None:
            self._VC = violationModularCuts(self)
        return self._VC


    def VD(self):
        """ ()

            returns a digraph that represents the additive structure
            of the alpha-violations in M
        """
        if self._VD is None:
            self._VD = encodeViolationsDigraph(self.V())
        return self._VD

    def VDC(self):
        """ ()

            returns a digraph that represents the modular-cut structure of
            the alpha-violations in M
        """
        if self._VDC is None:
            self._VDC = encodeViolationModularCuts(self)
        return self._VDC

    def __repr__(self):
        return repr(self.M) + ", with alpha support."

def decorateAlphaMatroid(M):
    """ (M)
        M __ matroid

        returns an AlphaMatroid(M) or M, depending whether M has been decorated
        or not.
    """
    if type(M) == AlphaMatroid:
        return M
    return AlphaMatroid(M)

### ---- ###


def violationModularCuts(M):
    """ (M)

        M __ matroid

        returns a violation-modular-cut dictionary
    """
    M = decorateAlphaMatroid(M)
    VC = {}
    for X in M.V():
        FMX = set(M.V()[X].keys())
        VC[X] = set(C.intersection(FMX) for C in M.modular_cuts())
    return VC

### ---- ###



def encodeViolationModularCuts(M):
    """ (M)

        M __ matroid

        returns a digraph that encodes how the modular cuts interact with
            the violations of M
    """
    M = decorateAlphaMatroid(M)
    D = DiGraph(loops=True)
    V = M.V()
    U = sorted(set(( (len(Y),Y,V[X][Y]) for X in V for Y in V[X] )))
    X0 = []
    for l, X, a in U:
        D.add_edge(X,X,a)
        X0.append(X)
        for Y in X0:
            if Y.issubset(X):
                D.add_edge(Y,X,0)
    X0 = frozenset(X0)
    cutNbr = 0
    for C in set((C.intersection(X0) for C in M.modular_cuts())):
        cutNbr += 1
        D.add_vertex(cutNbr)
        for X in C:
            D.add_edge(cutNbr, X, 1)

    return D


def encodeViolationsDigraph(V):
    """ (V)

        V __ violations dictionary
    """
    D = DiGraph(loops=True)
    U = sorted(set(( (len(Y),Y,V[X][Y]) for X in V for Y in V[X] )))
    X0 = []
    for l, X, a in U:
        D.add_edge(X,X,a)
        X0.append(X)
        for Y in X0:
            if Y.issubset(X):
                D.add_edge(Y,X,0)
    return D

def linearSubclassToModularCut(M,L):
    """ (M,L)

        M __ matroid
        L __ linear subclass

        returns the
            modular cut that corresponds to the linear subclass
    """
    H = frozenset(M.hyperplanes())
    L = frozenset(L)
    M0 = set()
    for F in allFlats(M):
        contained = True
        for h in H:
            if F.issubset(h):
                if not h in L:
                    contained = False
                    break
        if contained:
            M0.add(F)
    return M0

def getAllModularCuts(M):
    """ (M)

        M __ matroid

        returns all modular cuts of M, except the empty modular cut.
        (SAGE does not allow an extension with a coloop through M.extension !!)
    """
    H = frozenset(M.hyperplanes())
    L = [frozenset(l) for l in M.linear_subclasses()]
    Ms = [set() for l in L]
    for F in allFlats(M):
        for m,l in zip(Ms,L):
            contained = True
            for h in H:
                if F.issubset(h):
                    if not h in l:
                        contained = False
                        break
            if contained:
                m.add(F)

    return tuple(( frozenset(x) for x in Ms ))

def findViolations(M):
    """ (M)

        M __ matroid


        returns a dictionary D,
                where each key is a violation X in V(M)
    """
    M = decorateAlphaMatroid(M)
    alpha = M.alpha()
    weakViolations = set()
    depFlats = allDependentFlats(M)
    for a,X in zip(alpha[0],powerset(M.E)):
        if a < 0:
            weakViolations.add(frozenset(X))
    violations = getMinimalFamily(weakViolations)
    V = {}
    for X in violations:
        V[X] = {}
        for F in depFlats:
            if F.issubset(X):
                a = alpha[0][powersetSubsetIndex(F,M.E)]
                if a != 0:
                    V[X][F] = a
        V[X][X] = alpha[0][powersetSubsetIndex(X,M.E)]

    return V

def isInflated(M, X=None):
    """ (M, X=None)

        M __ matroid
        X __ (optionally) a subset of the groundset of M,
             X=M.groundset() by default
        returns a list of elements x from X that correspond to modular cuts
                of M.delete([x]) which are principal filters of a single flat.
    """
    inflated = []
    if X is None:
        X = M.groundset()
    for x in sorted(X):
        Mx = M.delete([x])
        C = set()
        if Mx.rank() < M.rank():
            continue #x is a coloop;
        for F in allFlats(Mx):
            if x in M.closure(F):
                C.add(F)
        C0 = getMinimalFamily(C)
        if len(C0) == 1:
            inflated.append(x)
    return inflated

def canonicalMatroidLabel(M):
    """ (M)

        M __ matroid

        returns the canonical label of the matroid M;
               which is a tuple
    """
    IS = IncidenceStructure(M.bases())
    phi = IS.canonical_label()

    return (frozenset((frozenset((phi[x] for x in B)) for B in M.bases())), len(M.groundset()))

### ---- ###


def findGammoidConstruction(M,vertexLimit=None,smart=True,Mlimit=-1):
    """ (M, vertexLimit=None)

        M __ matroid

        vertexLimit __ (optionally) max. number of elements of the strict gammoid

        returns either a strict gammoid N and a construction history how
                M may be constructed from N,
               or False
    """
    M = decorateAlphaMatroid(M)
    Md = decorateAlphaMatroid(M.dual())
    Md.history = "*"
    M.dualized = Md
    Md.dualized = M

    if vertexLimit is None:
        vertexLimit = vertexBound(len(M.E),M.rank())

    if len(M.E) > vertexLimit:
        return False
    if len(M.E) < vertexLimit:
        V = augmentList(M.E,vertexLimit - len(M.E))
    else:
        V = M.E
    if M.is_strict_gammoid():
        return M
    if Md.is_strict_gammoid():
        return M.dual(), "*"
    if easyRefute(M):
        return False, "refuted"
    if easyRefute(Md):
        return False, "refuted;*"

    head = [M,Md]
    Mcount = 0
    visited = set()
    visited.add(canonicalMatroidLabel(M)[0])
    visited.add(canonicalMatroidLabel(M.dual())[0])
    implicit = set()
    while head:
        print "Head: ",len(head)
        new_head = {}
        for M in head:
            if canonicalMatroidLabel(M) in implicit:
                continue
            print "M = ",M
            if len(M.E) >= len(V):
                continue
            e = V[len(M.E)]
            Ee = frozenset([e])
            for C0 in M.non_principal_modular_cuts():
                sys.stdout.flush()

                M0 = decorateAlphaMatroid(M.extension(element=e,subsets=C0))
                lbl = canonicalMatroidLabel(M0)[0]
                if not lbl in visited:
                    visited.add(lbl)
                    M0.history = ";"+M.history
                    M0d = decorateAlphaMatroid(M0.dual())
                    M0d.history = "*;"+ M0.history
                    lbld = canonicalMatroidLabel(M0d)[0]
                    visited.add(lbld)
                    if easyRefute(M0,Ee):
                        sys.stdout.write("-")
                        continue
                    if smart:
                        M0._alpha = calculateAlphaOfExtension(e,C0,M,M.alpha(),M.mu())
                    if M0.is_strict_gammoid():
                        return M0, M0.history
                    if easyRefute(M0d,Ee):
                        sys.stdout.write("-")
                        continue
                    if smart:
                        C0d = frozenset((F for F in allFlats(M.dualized) if e in M0d.closure(F)))
                        M0d._alpha = calculateAlphaOfExtension(e,C0d,M.dualized,M.dualized.alpha(),M.dualized.mu())
                    if M0d.is_strict_gammoid():
                        return M0d, M0d.history

                    M0d.dualized = M0
                    M0.dualized = M0d

                    Mcount += 1
                    if Mcount == Mlimit:
                        return False, "limit"
                    new_head[lbl] = M0
                    new_head[lbld] = M0d
                    sys.stdout.write("+")
                else:
                    sys.stdout.write(".")
            print "%"
        head = new_head.values()
    return False, "exhausted"

### ---- ###


def getDBlackBox(D,X,Y):
    """ (D,X,Y)

        D __ digraph
        X __ input vertices
        Y __ output vertices

        returns a matrix that codes lambda_(X,D,Y)
    """
    D = DiGraph(D)
    X = sorted(X)
    Y = sorted(Y)
    if frozenset(X).intersection(Y) != frozenset():
        raise "Error, X and Y must be disjoint!"
    M = Gammoid(D,Y,frozenset(X).union(Y))
    la = Matrix(2**len(Y),2**len(X))
    idx1 = -1
    for y in powerset(Y):
        idx1 += 1
        M0 = M.contract(frozenset(Y).difference(y))
        idx2 = -1
        for x in powerset(X):
            idx2 += 1
            la[idx1,idx2] = M0.rank(x)

    return la

def getMBlackBox(M, B=None):
    """ (M, B=None)

        M __ matroid

        B __ base of M (optional; otherwise use M.bases()[0])
    """
    if B is None:
        B = M.bases()[0]
    Y = sorted(B)
    X = sorted(M.groundset().difference(B))
    la = Matrix(2**len(Y),2**len(X))
    idx1 = -1
    for y in powerset(Y):
        idx1 += 1
        M0 = M.contract(frozenset(Y).difference(y))
        idx2 = -1
        for x in powerset(X):
            idx2 += 1
            la[idx1,idx2] = M0.rank(x)

    return la


### ---- ###


def searchForAcyclicDBlackBox(rho, internalNodes, searchAll=False, verbose=False, allowCyclic=False):
    """ (rho, internalNodes, searchAll=False)

        rho __ black box
        internalNodes __ number of internal nodes
        searchAll __ if True, return a list of all acyclic digraphs that
                     have the desired black box

        returns an acyclic digraph that has the black box rho;
                or None if exhaustive search failed.
    """
    nI = int( log_b(rho.dimensions()[0],2) )
    nO = int( log_b(rho.dimensions()[1],2) )
    internalNodes = int( internalNodes )
    print "Number of inputs:",nI
    print "Number of outputs:",nO
    I = ["i%d"%i for i in range(nI)]
    O = ["o%d"%i for i in range(nO)]
    X = ["x%d"%i for i in range(internalNodes)]
    V = I + O + X
    vI = [i for i in range(nI)]
    vO = [i+nI+internalNodes for i in range(nO)]

    xTails = [i for i in range(nI+internalNodes)]
    xHeads = [i+nI for i in range(nO+internalNodes)]

    print "Number of internal nodes:", internalNodes
    print "Number of possible arcs:", (nO+internalNodes)*(nI+internalNodes)
    V2idx = {}
    idx2V = {}
    for v,i in zip(V,range(len(V))):
        V2idx[v] = i
        idx2V[i] = v
    head = [DiGraph(len(V)).copy(immutable=True)]
    dboxes = []
    while head:
        new_head = set()
        print "Current Head Size:", len(head)
        first = True
        for D0 in head:
            if first:
                print " Nbr. of Arcs:",D0.num_edges()
                first = False
            la = getDBlackBox(D0, vI, vO)
            if max( [max(x) for x in list(la - rho)]) > 0:
                #overshoot
                if verbose:
                    print "Overshoot DiGraph; edge listing:"
                    for a,b,labl in D0.edges():
                        print "   ",idx2V[a], "->", idx2V[b]
                    print la -rho
                #dboxes.append(D0)
            else:
                if la == rho:
                    if searchAll:
                        print "Found DiGraph; edge listing:"
                        for a,b,labl in D0.edges():
                            print "   ",idx2V[a], "->", idx2V[b]
                        dboxes.append(D0)
                    else:
                        return D0
                else:
                    # try to add edge
                    for a in xTails:
                        for b in xHeads:
                            if a == b:
                                continue
                            if D0.has_edge(a,b):
                                continue
                            if not allowCyclic:
                                if D0.all_simple_paths([b],[a]):
                                    continue
                            D1 = D0.copy(immutable=False)
                            D1.add_edge(a,b)
                            new_head.add(D1.copy(immutable=True))
        head = new_head

    if searchAll:
        return dboxes
    return None

def to2dimTuple(M):
    """ (M)

        M __ matrix (or other kind of 2-dim array)

        returns a tuple of tuples of the contents of M
    """
    return tuple((tuple(x) for x in M))

def catalogueAcyclicDBlackBoxes(nI, nO, internalNodes, catalogue=None):
    """ (nI, nO, internalNodes, catalogue=None)

        nI __ number of inputs
        nO __ number of outputs
        internalNodes __ number of hidden layer nodes
        catalogue __ optional, a dictionary with previously found black boxes

        returns a dictionary that maps Matrix-tuples to one corresponding DBlackBox;
              i.e. to a tuple
    """
    if catalogue is None:
        catalogue = {}

    xIn = [i for i in range(nI)]
    xOut = [i for i in range]
    xTails = [i for i in range(nI+internalNodes)]
    xHeads = [i+nI for i in range(nO+internalNodes)]

    return catalogue

### ---- ###


class StashMatroid(BasisMatroid):
    pass

def canonicalMatroid(M):
    """ (M)

        M __ matroid

        returns a minor of M that has no loops, no coloops, no parallel edges
        and no coparallel edges
    """
    global canonicalMatroidStash
    if "canonical" in dir(M):
        return M
    M0 = M.delete(M.loops().union(M.coloops()))
    IS = IncidenceStructure(M0.bases())
    phi = IS.canonical_label()
    B0 = frozenset((frozenset((phi[x] for x in B)) for B in M0.bases()))
    if not B0 in canonicalMatroidStash:
        canonicalMatroidStash[B0] = StashMatroid(bases=B0,groundset=list((phi[x] for x in M0.groundset())))
        canonicalMatroidStash[B0].canonical = True
    return canonicalMatroidStash[B0]

### ---- ###


def getCoflowLattice(C):
    """ (C)

        C __ family of signed subsets of C


        returns a pair
            (E, L)
                where E is a list mapping the column indexes to their elements wrt. C
                and L is an IntegerLattice that corresponds to the coflow lattice of C
    """
    Co = getSignedCocircuits(C)
    E = sorted(set([x for x,s in uniteAll(Co)]))
    I = []
    for c in Co:
        V = [0 for e in E]
        for x,s in c:
            V[E.index(x)] = s
        I.append(V)
    L = IntegerLattice(I)
    return E, L

def getCatId(id):
    for M in canonicalMatroidStash.values():
        if "catid" in dir(M):
            if M.catid == id:
                return M
    return None

### ---- ###


def minimalViolationsOfHallCondition(A):
    """ (A)
        A __ dictionary: family of sets
        returns a list of all minimal violations of hall's condition for A
    """
    violations = []
    for X in powersetMinusO(A.keys()):
        nonMinimal = False
        for Y in violations:
            if Y.issubset(X):
                nonMinimal = True
                break
        if nonMinimal:
            continue
        X0 = uniteAll([A[x] for x in X])
        if len(X0) < len(X):
            violations.append(frozenset(X))
    return violations

### ---- ###



def oppositeDigraph(D):
    """ (D)

        returns the opposite digraph of D
    """
    D1 = DiGraph()
    for x in D.vertices():
        D1.add_vertex(x)
    for a,b,l in D.edges():
        D1.add_edge(b,a,l)
    return D1

def inverseMatroidInduction(D, T, M):
    """ (D, T, M)

        D __ digraph
        T __ set of targets
        M __ matroid that shall be induced from T

        returns a family of minimal sets of T that have to be dependent.
    """
    links = set()
    for R in allRoutingsBetween(D,T,M.groundset().intersection(D.vertices())):
        L = frozenset((p[0] for p in R))
        X = frozenset((p[-1] for p in R))
        links.add((L,X))
    C = set()
    for L,X in links:
        r = M.rank(L)
        C.update(combinations(X,r+1))

    return getMinimalFamily(C)

def testEliminationAxiom(C):
    """ (C)

        C __ family of circuits

        returns violations of the elimination axiom
    """
    C = setFamilize(C)
    violations = []
    for Q in combinations(C,2):
        Q0 = Q[0].union(Q[1])
        for e in Q[0].intersection(Q[1]):
            good = False
            for c in C:
                if e in c:
                    continue
                if c.issubset(Q0):
                    good = True
                    break
            if not good:
                violations.append((Q[0],e,Q[1]))
    return violations

def hasObviousNonGammoidMinor(M):
    """ (M)

        returns true, if M or M.dual() has a rank 3 minor that is not a strict gammoid
    """
    if M.rank() < 3:
        return False
    Md = M.dual()
    if Md.rank() < 3:
        return False
    for I in M.independent_r_sets(M.rank()-3):
        if min(getAlphaSystem(M.contract(I)).values()) < 0:
            return True
    for I in Md.independent_r_sets(Md.rank()-3):
        if min(getAlphaSystem(M.contract(I)).values()) < 0:
            return True
    return False

def DigraphInducedMatroid(D, T, E=None):
    """
        (D, T, E=None)

        D __ digraph
        T __ matroid
        E __ (optionally) vertices of the induced matroid

         returns the induced wrt. to the digraph D,
         the target matroid T,
         and the set of matroid elements E.

         If E==None, then E=V is used.
    """
    if type(D) != sage.graphs.digraph.DiGraph:
        D = DiGraph(D,loops=False)
    if E is None:
        E = list(D.vertices())
    S = list(T.groundset().intersection(D.vertices()))
    P = {}
    for e in E:
        for s in S:
            P[(e,s)] = set()
    for p in D.all_simple_paths(E, S, trivial=True):
        e = p[0]
        s = p[-1]
        P[(e,s)].add(frozenset(p))

    F0 = set()
    for e in E:
        for s in S:
            for p in P[(e,s)]:
                F0.add((frozenset([e]),frozenset([s]),p))
    while F0:
        F1 = F0
        F0 = set()
        for (src,dst,vtx) in F1:
            for e in E:
                if e in src:
                    continue
                for s in S:
                    if s in dst:
                        continue
                    dst2 = dst.union([s])
                    if T.is_dependent(dst2):
                        continue
                    for p in P[(e,s)]:
                        if not p.intersection(vtx):
                            F0.add((src.union( (e,) ), dst2, vtx.union(p)))
    bases = set()
    for src,dst,vtx in F1:
        bases.add(src)
    return BasisMatroid(groundset=E, bases=bases)

def BiApexMatroid(k):
    """ (k)

        k __ Parameter k, k>= 2

        returns the bi-apex matroid B(k)
    """
    if k < 2:
        k = 2
    X = [(i,i) for i in range(k)]+[(i,i+1) for i in range(k-1)] + [(k-1,0)]
    E = ["a","b"] +X
    H = [["a",(i,i),(i,i+1)] for i in range(k-1)] + [["a",(k-1,k-1),(k-1,0)]] \
     + [["b",(i+1,i+1),(i,i+1)] for i in range(k-1)] + [["b",(k-1,0),(0,0)]]
    return CircuitClosuresMatroid(groundset=E,circuit_closures={3:[E],2:H})

def backtrackBipartiteInduction(M,N):
    """ (M, N)

        M __ matroid
        N __ matroid

        returns a set D of pairs (p,q), such that X is independent in M
        if it can be matched to an independent set Y of N using arcs from D
        or None if this is not possible
    """
    E = sorted(M.groundset())
    B = frozenset(M.bases())
    F = sorted(N.groundset())
    D = list()
    Matchings = []
    idxMatchings = []
    Indeps = []
    idxIndeps = []
    arc = [-1,0]
    backtrack = False
    iteration = 0
    count = 2**(len(E)*len(F))
    while 1:
        #print D
        arc[0] += 1
        if arc[0] == len(E):
            arc[0] = 0
            arc[1] += 1
            if arc[1] == len(F):
                backtrack = True
        if backtrack:
            if len(D) == 0:
                return None
            arc[0], arc[1] = D.pop()

            del Matchings[idxMatchings.pop():]
            del Indeps[idxIndeps.pop():]


        if not backtrack:
            iteration += 1
            if iteration % 2500 == 0:
                print "\r d=",len(D),"i=",iteration," I=",len(Indeps)," B=",len(B.difference(Indeps)),"   ",
                sys.stdout.flush()
            e = E[arc[0]]
            f = F[arc[1]]
            #print D, e,f
            #print Matchings
            #print Indeps
            #if not N.is_independent([f]): #useless to add
            #    continue
            #if not M.is_independent([e]): #useless, too.
            #    continue
            D.append(tuple(arc))
            idxMatchings.append(len(Matchings))
            idxIndeps.append(len(Indeps))
            current = set(Matchings)
            currentI = set(Indeps)
            Matchings.append((frozenset([e]),frozenset([f])))
            newMatchings = []
            if not frozenset([e]) in Indeps:
                Indeps.append(frozenset([e]))
            newIndeps = []
            overshoot = False
            for L,R in Matchings:
                if e in L:
                    continue
                if f in R:
                    continue
                L1 = L.union([e])
                R1 = R.union([f])
                if not N.is_independent(R1):
                    continue
                if not M.is_independent(L1):
                    overshoot = True
                    break
                if not (L1,R1) in current:
                    current.add((L1,R1))
                    newMatchings.append((L1,R1))
                    if not L1 in currentI:
                        currentI.add(L1)
                        newIndeps.append(L1)
            if not overshoot:
                Matchings.extend(newMatchings)
                Indeps.extend(newIndeps)
                if len(B.difference(Indeps)) == 0:
                    return D
            else:
                arc_nbr = (arc[0] + arc[1]*len(E))
                sys.stdout.flush()
                backtrack = True
        else:
            backtrack = False

def isStrongBaseOrderable(M, E0=None):
    """ (M, E0=None)

         M __ matroid

         E0 __ optionally a subset of the groundset of M;
               such that the property of strong base-orderability is not tested
               for base pairs that do not contain at least one element of E0

        return False if there are bases B1,B2 where B1.union(B2).intersection(E0) is
        not empty, such that there is no bijection phi between B1.difference(B2)
        and B2.difference(B1) with the property that for every subset X of B1,
        B1.difference(X).union(phi[X]) is a base of M.
        (E0 is useful for single-element extensions).
    """

    if E0 is None:
        E0 = M.groundset()
    MB = frozenset(M.bases())
    for B1,B2 in combinations(MB,2):
        B1 = frozenset(B1)
        if not E0.intersection(B1.union(B2)):
            continue
        L = list(B1.difference(B2))
        R = list(frozenset(B2).difference(B1))

        foundP = False
        for p in Permutations(len(L)):
            good = True
            for Y in powersetMinusOI(range(len(L))):
                B = B1.difference([L[i] for i in Y]).union([ R[p(i+1)-1] for i in Y ])
                if not B in MB:
                    good = False
                    break
            if good:
                foundP = True
                break
        if not foundP:
            return False
    return True


def ingletonViolation(M,sloppy=None):
    """ (M, sloppy= None)

        M __ matroid

        tests the violation of the Ingleton condition for singleton sets W,X,Y,Z

        sloppy __ (optionally) set a maximum cardinality for W,X,Y, and Z each.

        returns (W,X,Y,Z) if Ingleton's condition is violated for such a tuple,
        or None.
    """
    if sloppy is None:
        sloppy = M.rank()
    E = []
    for i in range(2,sloppy+1):
        E.extend(M.independent_r_sets(i))
    for x in E:
        for y in E:
            if y == x:
                continue
            for z in E:
                if z==x or z==y:
                    continue
                for w in E:
                    if w == x or w == y or w == z:
                        continue
                    if M.rank(w) + M.rank(x) + M.rank(w.union(x,y)) + M.rank(w.union(x,z)) + M.rank(y.union(z)) > \
                    M.rank(w.union(x)) + M.rank(w.union(y)) + M.rank(w.union(z)) + M.rank(x.union(y)) + M.rank(x.union(z)):
                        return (w,x,y,z)
    return None


def isElementInduced(M, e):
    """ (M, e)

        M __ matroid

        e __ element of the groundset

        tests, whether the element e is induced from M.delete([e])
              by a digraph. (Which then is a digraph on M.groundset(), such
              that the only non-sink is the element e)
    """
    MB = frozenset(M.bases())
    eB = frozenset([X for X in MB if e in X])
    M0 = M.delete([e])
    allowedTargets = set()
    E0 = M.groundset().difference([e])
    for e0 in E0:
        M00 = M0.contract([e0])
        notGood = False
        for B in M00.bases():
            if M.is_dependent(B.union([e])):
                notGood = True
                break
        if notGood == False:
            allowedTargets.add(e0)
    for B in eB:
        if M.rank(B.difference([e]).union(allowedTargets)) < len(B):
            return False
    return True

def isStrictGammoid(M):
    """ (M)

        M __ matroid

        return False if M is not a strict gammoid,
           and True if it is.
    """
    alpha = {}
    for x in allDependentFlats(M):
        nlt = len(x) - M.rank(x)
        for y in alpha:
            if y.issubset(x):
                nlt -= alpha[y]
        if nlt < 0:
            return False
        alpha[x] = nlt
    nonZero = frozenset([x for x in alpha.keys() if alpha[x] > 0])
    testSets = set()
    for i in range(2,len(nonZero)):
        for Q in combinations(nonZero,i):
            testSets.add(uniteAll(Q))
    for x in testSets.difference(alpha.keys()):
        nlt = len(x) - M.rank(x)
        for y in alpha:
            if y.issubset(x):
                nlt -= alpha[y]
        if nlt < 0:
            return False
    return True

def hasNonStrictRk3Minor(M):
    """ (M)

        M __ matroid
    """
    if M.rank() < 3:
        return False
    for I in M.independent_r_sets(M.rank()-3):
        if not isStrictGammoid(M.contract(I)):
            return True
    return False


def classifySingleElementExtensions(M,x=-1):
    """ (M, x="-1")

        M __ matroid

        x __ name of the new element, defaults to -1

        returns a dictionary, where the values are lists representatives
                of isomorphism classes of single element extensions of M.
    """
    found = set()
    categories = {"strict gammoid":[],"transversal matroid":[],
                "non base-orderable":[],
                  "non-strict rk 3 minor":[],
                  "non-strict co-rk 3 minor":[],
                  "induced extension":[],
                  "undecided":[],"induced non-gammoid":[],
                  "induces undecided":[],
                  "induces undecided induced":[]}
    for Mx in M.extensions(x):
        cl = canonicalMatroidLabel(Mx)
        if cl in found:
            sys.stdout.write(".")
            sys.stdout.flush()
            continue
        found.add(cl)
        if isStrictGammoid(Mx):
            categories["strict gammoid"].append(Mx)
            sys.stdout.write("G")
            sys.stdout.flush()
            continue
        if isStrictGammoid(Mx.dual()):
            categories["transversal matroid"].append(Mx)
            sys.stdout.write("T")
            sys.stdout.flush()
            continue
        if isStrongBaseOrderable(Mx,frozenset([x])) == False:
            categories["non base-orderable"].append(Mx)
            sys.stdout.write("s")
            if isElementInduced(Mx,x):
                sys.stdout.write("!")
                categories["induced non-gammoid"].append(Mx)
            sys.stdout.flush()
            continue
        if hasNonStrictRk3Minor(Mx):
            categories["non-strict rk 3 minor"].append(Mx)
            sys.stdout.write("m")
            if isElementInduced(Mx,x):
                sys.stdout.write("!")
                categories["induced non-gammoid"].append(Mx)
            sys.stdout.flush()
            continue
        if hasNonStrictRk3Minor(Mx.dual()):
            categories["non-strict co-rk 3 minor"].append(Mx)
            sys.stdout.write("d")
            if isElementInduced(Mx,x):
                sys.stdout.write("!")
                categories["induced non-gammoid"].append(Mx)
            sys.stdout.flush()
            continue
        if isElementInduced(Mx,x):
            categories["induced extension"].append(Mx)
            sys.stdout.write("*")
            for x in M.groundset():
                if isElementInduced(Mx,x):
                    Mxx = Mx.delete(x)
                    lbl = canonicalMatroidLabel(Mxx)
                    if not lbl in found:
                        found.add(lbl)
                        sys.stdout.write("$")
                        categories["induces undecided induced"].append(Mxx)
            sys.stdout.flush()
            continue

        categories["undecided"].append(Mx)
        sys.stdout.write("?")
        if hasInducedElement(Mx):
            for x in Mx.groundset():
                if isElementInduced(Mx,x):
                    Mxx = Mx.delete(x)
                    lbl = canonicalMatroidLabel(Mxx)
                    if not lbl in found:
                        found.add(lbl)
                        sys.stdout.write("$")
                        categories["induces undecided"].append(Mxx)
        sys.stdout.flush()

    print "... \n stats: \n"
    classificationStats(categories)
    print "done."
    return categories

def hasInducedElement(M):
    """ (M)

        M __ matroid

        returns [e] if M has at least one induced element e,
        or [] otherwise
    """
    for e in M.groundset():
        if isElementInduced(M,e):
            return [e]
    return []

### ---- ###


def relaxHyperplane(M, H):
    """ (M, H)

        M __ matroid
        H __ circuit hyperplane

        returns the relaxed matroid"""
    if M.rank(H) != M.rank()-1:
        raise Exception("H is not a hyperplane!")
    if len(H) != M.rank():
        raise Exception("H is not a circuit!")
    H = frozenset(H)
    cc = M.circuit_closures()
    cc[M.rank()-1] = cc[M.rank()-1].difference([H])
    return CircuitClosuresMatroid(circuit_closures=cc,groundset=M.groundset())

### ---- ###


def checkClassForInduceds(C):
    """ (C)

        C __ list of matroids

        returns a list of matroids from C and duals of matroids from C
                which have induced elements
    """
    ind = []
    for M in C:
        if hasInducedElement(M):
            ind.append(M)
        elif hasInducedElement(M.dual()):
            ind.append(M)
    return ind

def getAllInducedAndDuallyInducedElements(M):
    """ (M)

        M __ matroid

        returns a pair of lists, where the first component consists of
        the induced elements of M, and the second component consists of the
        induced elemens of M.dual()
    """
    Md = M.dual()
    a,b = [],[]
    for e in M.groundset():
        if isElementInduced(M,e):
            a.append(e)
        if isElementInduced(Md,e):
            b.append(e)
    return a,b

def classificationStats(D):
    for x in D.keys():
        print x,len(D[x])

### ---- ###


def permutateVector(a, G0, phi):
    """ (a, G0, phi)

        rearranges an alpha vector with respect to the new names given by ph
    """
    b = Matrix(1,2**len(G0))
    G0 = sorted(G0)
    G1 = sorted([phi[g] for g in G0])
    phiInv = dict(((phi[g],g) for g in G0))
    idx = -1
    for L in powerset(G1):
        L0 = [phiInv[l] for l in L]
        idx += 1
        b[0,idx] = a[0,powersetSubsetIndex(L0,G0)]
    return b
def unpermutateVector(a, G0, phi):
    """(a, G1, phi)

        rearranges an alpha vector with respect to the old names
    """
    b = Matrix(1,2**len(G0))
    G0 = sorted(G0)
    G1 = sorted([phi[g] for g in G0])
    idx = -1
    for L in powerset(G0):
        L1 = [phi[l] for l in L]
        idx += 1
        b[0,idx] = a[0,powersetSubsetIndex(L1,G1)]
    return b
def unpermutateMatrix(a, G0, phi):
    """ (a, G0, phi)

        rearranges an mu matrix with respect to the old names
    """
    b = Matrix(2**len(G0),2**len(G0))
    G0 = sorted(G0)
    G1 = sorted([phi[g] for g in G0])
    idx = -1
    for L in powerset(G0):
        L1 = [phi[l] for l in L]
        ridx = powersetSubsetIndex(L1,G1)
        idx += 1
        idx1 = -1
        for M in powerset(G0):
            M1 = [phi[m] for m in M]
            idx1 += 1
            b[idx1,idx] = a[powersetSubsetIndex(M1,G1),ridx]
    return b

class GammaM(object):
    def __init__(self, M0=None):
        """ (M0=None)

            M0 __ (optionally)
                    initial target matroid

            creates a GammaM decider
        """
        self.targets = set() # stop loop if no targets are there
        self.nonGammoids = set() # classes that are gammoids
        self.gammoids = set() # classes that are not gammoids
        self.exhausted = set() # classes that have been extended already

        self.nonGammoidTestFamily = []
        try:
            fromoutside = set([canonicalMatroid(M.M) for M in easyRefute.NonGammoids])
            fromoutsided = set([canonicalMatroid(M.dual()) for M in fromoutside])
            self.nonGammoidTestFamily = list(fromoutside.union(fromoutsided))
        except:
            pass

        self.implications = set() #special implications

        self.equalclasses = {}

        self.layers = [] # classes in layers
        self.distance = {} # distance to the next target

        self.classes = {}
        self.invClasses = {}
        self.classId = 1
        self.representatives = {}

        self.upperVertexBound = 100

        self.addTarget(M0)

    def __repr__(self):
        return "GammaM-decider."

    def auto(self):
        s0 = list(self.targets)
        while self.targets:
            self.nextStep()
            for M in s0:
                if not M in self.targets:
                    print M," G?",self.gammoids[self.classes[M]]," nG?",self.nonGammoids[self.classes[M]]


    def unsetDistance(self, cid):
        if cid in self.distance:
            d = self.distance.pop(cid)
            self.layers[d].discard(cid)

    def setDistance(self, cid, d):
        self.unsetDistance(cid)
        self.distance[cid] = d
        if len(self.layers) <= d:
            for i in range(len(self.layers),d+1):
                self.layers.append(set())
        self.layers[d].add(cid)

    def getNextClass(self):
        ignore = self.gammoids.union(self.nonGammoids).union(self.exhausted)
        for l in self.layers:
            l0 = l.difference(ignore)
            if l0:
                return l0.__iter__().next()
        return None

    def hasTargets(self):
        return len(self.targets) > 0

    def isNonGammoid(self,M,E0=None):
        M = canonicalMatroid(M)
        if E0 is None:
            for N in self.nonGammoidTestFamily:
                if M.has_minor(N):
                    return True
        elif E0 is not False:
            for N in self.nonGammoidTestFamily:
                if hasMinorWith(M,N,E0):
                    return True
        if M.rank() == 3:
            if not "alpha" in dir(M):
                M.alpha = alphaVector(M)
            return min(M.alpha[0]) < 0
        return False

    def isGammoid(self,M):
        M = canonicalMatroid(M)
        if not "alpha" in dir(M):
            sys.stdout.write("a")
            sys.stdout.flush()
            M.alpha = alphaVector(M)
            sys.stdout.write(";")
            sys.stdout.flush()
        return min(M.alpha[0]) >= 0

    def updateMinorTest(self,cid):
        for l,M in sorted([(len(M.groundset()),M) for M in self.invClasses[cid]]):
            minimal = True
            for N in self.nonGammoidTestFamily:
                if M.has_minor(N):
                    minimal = False
                    break
            if minimal:
                new_test_family = [M]
                for N in self.nonGammoidTestFamily:
                    if not N.has_minor(M):
                        new_test_family.append(N)
                self.nonGammoidTestFamily = new_test_family


    def newNonGammoid(self,cid):
        cidlist = set([cid])
        while cidlist:
            cid = cidlist.pop()
            self.nonGammoids.add(cid)
            self.targets.discard(cid)
            new_implications = set()
            for A in self.implications:
                if (cid,"C") in A:
                    continue
                A0 = A.difference([cid])
                if len(A0) == 1:
                    cid2 = A0.__iter__().next()[0]
                    cidlist.add(cid2)
                else:
                    new_implications.add(A0)
            self.implications = new_implications
            self.updateMinorTest(cid)

    def newGammoid(self,cid):
        cidlist = set([cid])
        while cidlist:
            cid = cidlist.pop()
            self.gammoids.add(cid)
            self.targets.discard(cid)
            new_implications = set()
            for A in self.implications:
                if (cid,"C") in A:
                    continue
                if cid in A:
                    for x in A:
                        try:
                            if x[1] == "C":
                                cidlist.add(x[0])
                        except:
                            pass
                else:
                    new_implications.add(A)
            self.implications = new_implications

    def canDecide(self,M,cid):
        if self.isNonGammoid(M):
            self.newNonGammoid(cid)
            return True
        if self.isNonGammoid(M.dual()):
            self.newNonGammoid(cid)
            return True
        if self.isGammoid(M):
            self.newGammoid(cid)
            return True
        if self.isGammoid(M.dual()):
            self.newGammoid(cid)
            return True
        return False

    def nextStep(self):
        if self.hasTargets():
            for l in self.layers:
                l0 = l.difference(self.gammoids).difference(self.nonGammoids).difference(self.exhausted)
                if l0:
                    cid = l0.__iter__().next()
                    print "Visiting ",cid, " d=",self.distance[cid]
                    self.visitClass(cid)
                    return

    def deflateClass(self,cid):
        M = self.representatives[cid]
        Md = canonicalMatroid(M.dual())
        #try to deflate
        did_deflate = 0
        for i in range(2):
            G = sorted(M.groundset())
            deflates = set()
            for DL in getDeflationList(M):
                Mdel = canonicalMatroid(M.delete(DL))
                deflates.add(Mdel)
                if Mdel in self.classes:
                    cidel = self.classes[Mdel]
                    if cidel in self.gammoids:
                        newGammoid(cid)
                    if cidel in self.nonGammoids:
                        newNonGammoid(cid)
                    self.combineClasses(cid,cidel)
                else:
                    cidel = self.updateGammoidClass(Mdel)
                    self.setDistance(cidel,self.distance[cid])
                    if self.canDecide(cidel,Mdel):
                        if cidel in self.gammoids:
                            newGammoid(cid)
                        if cidel in self.nonGammoids:
                            newNonGammoid(cid)
                    self.combineClasses(cid,cidel)
            M,Md = Md,M
            did_deflate += len(deflates)
            if M == Md:
                break
        if did_deflate:
            print "deflated ", did_deflate, "classes"
            sys.stdout.flush()
            return True
        return False

    def visitClass(self,cid, debug=0):
        M = self.representatives[cid]
        if debug < 1:
            if self.canDecide(M,cid):
                print "could decide"
                sys.stdout.flush()
                return
        if debug < 2:
            if self.deflateClass(cid):
                return
        Md = canonicalMatroid(M.dual())

        # try to augment matroid/& dual
        if debug < 3:
            e = len(M.groundset())
            print "augmenting ",M
            if e < self.upperVertexBound:
                if M.rank() > Md.rank():
                    print "...using dual"
                    M,Md = Md,M

                extension_ids = set()
                for Mx in M.extensions(element=e):
                    C0 = frozenset((F for F in allFlats(M) if e in Mx.closure(F)))
                    F0 = set(M.groundset())
                    for F in C0:
                        F0.intersection_update(F)
                        if F0 not in C0 or (not F0):
                            break
                    if F0 in C0:
                        continue # extension with principal modular cut
                    Mx0 = Mx
                    Mx = canonicalMatroid(Mx)
                    xid = self.updateGammoidClass(Mx)

                    if not xid:
                        sys.stdout.write(".")
                        sys.stdout.flush()
                        xid = self.classes[Mx]
                        if xid == cid:
                            continue
                        if xid in self.gammoids:
                            newGammoid(cid)
                            return
                        if xid in self.nonGammoids:
                            continue
                    else:
                        if self.isNonGammoid(Mx0,E0=frozenset([e])):
                            sys.stdout.write("-")
                            self.newNonGammoid(xid)
                            continue
                        if self.deflateClass(xid):
                            extensions_ids.add(xid)
                            continue

                        if len(Mx.groundset()) == len(Mx0.groundset()):
                            if not "alpha" in dir(Mx):
                                # use smart alpha calulculation
                                if not "alpha" in dir(M):
                                    M.alpha = alphaVector(M)
                                if not "mu" in dir(M):
                                    M.mu = moebiusMatrixForAlphaPoset(M)
                                alpha0 = calculateAlphaOfExtension(e,C0,M,M.alpha,M.mu)
                                IS = IncidenceStructure(Mx0.bases())
                                phi = IS.canonical_label()
                                Mx.alpha = permutateVector(alpha0,Mx0.groundset(),phi)
                                sys.stdout.write("+")
                                #if Mx.alpha != alphaVector(Mx):
                                #    raise Exception("ERROR!")
                                #else:
                                #    sys.stdout.write("^")
                                #    print phi
                            else:
                                sys.stdout.write("@")

                        else:
                            sys.stdout.write("!")
                        sys.stdout.flush()
                        self.setDistance(xid,self.distance[cid] + 1)

                    extension_ids.add(xid)
                    #C0 = frozenset((F for F in allFlats(M) if e in Mx.closure(F)))
                    #Mxd = Mx.dual()
                    #C0d = frozenset((F for F in allFlats(Md if e in Mxd.closure(F))))

                if not extension_ids:
                    newNonGammoid(self.equalclasses[cid])
                    return
                else:
                    extension_ids = set((self.equalclasses[x]
                            for x in extension_ids)).difference([self.equalclasses[cid]])
                    extension_ids.add((self.equalclasses[cid],"C"))
                    if len(extension_ids) > 0:
                        self.implications.add(frozenset(extension_ids))
                    else:
                        raise Exception(" Self-Referential Extension Set! ")
                sys.stdout.write("%\n")
                sys.stdout.flush()

            self.exhausted.add(cid)





    def combineClasses(self, c1, c2):
        """ combine two classes into one """
        if c1 == c2:
            return
        M1 = self.representatives[c1]
        M2 = self.representatives[c2]
        c = min(c1,c2)
        c0 = max(c1,c2)
        self.equalclasses[c0] = c
        d1 = self.distance[c1]
        d2 = self.distance[c2]
        d = min(d1,d2)
        self.unsetDistance(c0)
        self.setDistance(c,d)
        if len(M1.groundset()) < len(M2.groundset()):
            M = M1
            exC = c1
            exC0 = c2
        elif len(M1.groundset()) == len(M2.groundset()):
            if (M1.rank() < M2.rank()):
                M = M1
                exC = c1
                exC0 = c2
            elif M1.rank() == M2.rank():
                if d1 <= d2:
                    M = M1
                    exC = c1
                    exC0 = c2
                else:
                    M = M2
                    exC = c2
                    exC0 = c1
            else:
                M = M2
                exC = c2
                exC0 = c1
        else:
            M = M2
            exC = c2
            exC0 = c1
        self.representatives.pop(c0)
        self.representatives[c] = M
        for Mx in self.invClasses[c0]:
            self.classes[Mx] = c
        self.invClasses[c].update(self.invClasses[c0])
        self.invClasses.pop(c0)
        new_implications = set()
        trivial = set([c0,(c,"C")])
        trivial2 = set([c,(c0,"C")])
        removed_trivial = False
        for A in self.implications:
            if trivial.issubset(A) or trivial2.issubset(A):
                removed_trivial = True
                continue
            if c0 in A:
                new_implications.add(A.difference([c0]).union([c]))
                A.add(c)
            if (c0,"C") in A:
                new_implications.add(A.difference([(c0,"C")]).union([(c,"C")]))
        if removed_trivial:
            if (not c in self.exhausted) or (not c0 in self.exhausted):
                self.exhausted.difference_update([c,c0])
        if exC0 in self.exhausted:
            self.exhausted.remove(exC0)
        self.implications = new_implications
        if c0 in self.targets:
            self.targets.remove(c0)
            self.targets.add(c)
        if c0 in self.gammoids:
            self.gammoids.remove(c0)
            self.gammoids.add(c)
        if c0 in self.nonGammoids:
            self.nonGammoids.remove(c0)
            self.nonGammoids.add(c)

    def updateGammoidClass(self, M):
        M0 = canonicalMatroid(M)
        if not M0 in self.classes:
            M0d = canonicalMatroid(M0.dual())
            M0.dual = lambda y=0,x=M0d: x
            M0d.dual = lambda y=0,x=M0: x
            self.classes[M0] = self.classId
            self.classes[M0d] = self.classId
            self.representatives[self.classId] = M0
            if M0 != M0d:
                self.invClasses[self.classId] = set([M0,M0d])
            else:
                self.invClasses[self.classId] = set([M0])
            self.equalclasses[self.classId] = self.classId
            self.classId += 1
            return self.classId - 1
        else:
            return 0


    def addTarget(self, M):
        M0 = canonicalMatroid(M)
        self.updateGammoidClass(M0)
        cid = self.classes[M0]
        if cid in self.nonGammoids or cid in self.gammoids or cid in self.targets:
            return
        self.targets.add(cid)
        self.setDistance(cid,0)

### ---- ###


def getAlpha(M,X):
    """ (M,X)

        M __ matroid
        X __ subset of the groundset

        returns alpha_M(X), the value of Mason's alpha function for the set X
    """
    X = frozenset(X)
    F0 = sorted([(M.rank(F),F) for F in allDependentFlats(M) if F.issubset(X)])
    alpha = {}
    for r,F in F0:
        alphaF = len(F) - M.rank(F)
        for G in alpha.keys():
            if G.issubset(F):
                alphaF -= alpha[G]
        alpha[F] = alphaF
    if M.is_closed(X):
        return alpha[X]
    else:
        return len(X) - M.rank(X) - sum(alpha.values())

def cmpWrtFlats(l,r,flats):
    """ (l,r, flats)

        l,r __ operands

        flats __ set/family of frozensets

        compares whether l is a subset of r, and if l is a proper subset,
                whether l in flats
    """
    l = frozenset(l)
    r = frozenset(r)
    if l == r:
        return 0
    if len(l) > len(r):
        return -cmpSome(r,l,flats)
    if not l.issubset(r):
        return 0
    if not l in flats:
        return 0
    return -1

def leqWrtFlats(l,r,flats):
    """ (l,r, flats)

        l,r __ operands

        flats __ set/family of frozensets

        compares whether l is a subset of r, and if l is a proper subset,
                whether l in flats;
                returns True if l <=(flats) r.
    """
    l = frozenset(l)
    r = frozenset(r)
    if l == r:
        return True
    if not l.issubset(r):
        return False
    if not l in flats:
        return False
    return True

def downsetWrtFlats(r,flats):
    """ (r,flats)

       r __ operand

       flats __ set/family of frozensets

       returns the subsets l of r, for which l <=(flats) r holds.
    """
    r = frozenset(r)
    return frozenset([r] + [l for l in flats if l.issubset(r)])



def alphaPosetCmp(M):
    """ (M)

        M __ matroid

        returns a function that implements cmp for the alpha_M poset.
        (use it with care! a return value of 0 may be equal or incomparable!
         but it is nice for sorting stuff)
    """
    return lambda l,r,f=frozenset(allFlats(M)): cmpWrtFlats(l,r,f)

def alphaPosetLeq(M):
    """ (M)

        M __ matroid

        returns a function that compares whether l <= r with respect to
                the alpha_M poset, and then returns either True of False
    """
    return lambda l,r,f=frozenset(allFlats(M)): leqWrtFlats(l,r,f)

def alphaPosetDownsets(M):
    """ (M)

        M __ matroid

        returns a function that gives the downsets of the alpha_M poset
    """
    return lambda r,f=frozenset(allFlats(M)): downsetWrtFlats(r,f)

def extensionFlats(M, C, e, viaSage=False):
    """ (M, C, e, viaSage=False)

            M __ matroid
            C __ minimal elements of a modular cut of M
            e __ name of the extension element

            viaSage __ if True, then use a matroid extension combined with allFlats;
                        otherwise, calculate directly

            returns the family of flats of M extended by e corresponding to the cut C
    """
    if viaSage:
        N = M.extension(e, C)
        return frozenset(allFlats(N))
    FM = frozenset(allFlats(M))
    Cx = set()
    for c in setFamilize(C):
        for F in FM:
            if F.issuperset(c):
                Cx.add(F)
    Cx = frozenset(Cx)
    Below = frozenset((F for F in FM if not F in Cx))
    NonCovered = set()
    for F in Below:
        covered = False
        for x in M.groundset().difference(F):
            if M.closure(F.union([x])) in Cx:
                covered = True
                break
        if not covered:
            NonCovered.add(F)
    return FM.difference(Cx).union((x.union([e]) for x in Cx)).union(x.union([e]) for x in NonCovered)

def modularCutOfElement(M,e):
    """ (M, e)

        M __ matroid
        e __ element of M

        returns the modular cut of M\\e that restores M.
    """
    return frozenset( X.difference([e]) for X in allFlats(M) if e in M.closure(X.difference([e])))

def alphaPrimePosetLeq(M, C, e, viaSage=False):
    """ (M, C, e)

        M __ matroid
        C __ minimal elements of a modular cut of M
        e __ name of the extension element

        viaSage __ if True, use a matroid extension and alphaPosetDownset

        returns a function that gives the downsets of the alpha_N poset,
                that corresponds to the single element extenion of M by e
                that is described by the modular cut C.
    """
    if viaSage:
        return alphaPosetLeq(M.extension(e,C))
    return lambda r,f=extensionFlats(M,C,e): leqWrtFlats(r,f)

def alphaPrimePosetCmp(M, C, e, viaSage=False):
    """ (M, C, e)

        M __ matroid
        C __ minimal elements of a modular cut of M
        e __ name of the extension element

        viaSage __ if True, use a matroid extension and alphaPosetDownset

        returns a function that gives the downsets of the alpha_N poset,
                that corresponds to the single element extenion of M by e
                that is described by the modular cut C.
    """
    if viaSage:
        return alphaPosetCmp(M.extension(e,C))
    return lambda r,f=extensionFlats(M,C,e): cmpWrtFlats(r,f)


def alphaPrimePosetDownsets(M, C, e, viaSage=False):
    """ (M, C, e)

        M __ matroid
        C __ minimal elements of a modular cut of M
        e __ name of the extension element

        viaSage __ if True, use a matroid extension and alphaPosetDownset

        returns a function that gives the downsets of the alpha_N poset,
                that corresponds to the single element extenion of M by e
                that is described by the modular cut C.
    """
    if viaSage:
        return alphaPosetDownsets(M.extension(e,C))
    return lambda r,f=extensionFlats(M,C,e): downsetWrtFlats(r,f)


def zetaMatrixForAlphaPoset(M):
    """ (M)

        M __ matroid

        returns the zeta matrix of the alpha_M poset.
    """
    nG = len(M.groundset())
    zeta = Matrix(2**nG,2**nG,sparse=True)
    idx1 = -1
    leq = alphaPosetLeq(M)
    for L in powerset(M.groundset()):
        idx1 += 1
        idx2 = -1
        for R in powerset(M.groundset()):
            idx2 += 1
            if leq(L,R):
                zeta[idx1,idx2] = 1
    return zeta

def powersetSubsetIndex(S, X):
    """ (S, X)

        S __ subset of X
        X __ universe (list or implicitly sorted)

        returns the iteration index where the subset S occurs in the powerset
        iterator
    """
    if type(X) != list:
        X = sorted(X)
    #cfs = binomial_coefficients(len(X))
    idx0 = 0
    for i in range(len(S)):
        idx0 += binomial(len(X),i)
    idx00 = idx0
    idxs = sorted((X.index(s) for s in S))
    x0 = 0
    s0 = 0
    for i in idxs:
        for j in range(x0,i):
            # add number of choices where j is fixed at position s0;
            # consequently, the subsequent numbers must be bigger than j.
            idx0 += binomial(len(X) - j -1, len(S) - s0 - 1)
        s0 += 1
        x0 = i + 1
    return idx0

def moebiusMatrixForAlphaPoset(M):
    """ (M)

        M __ matroid

        returns the Moebius-function of the alpha_M poset.
    """
    G = sorted(M.groundset())
    nG = len(G)
    mu = Matrix(2**nG,2**nG,sparse=True)
    idx1 = -1
    leq = alphaPosetLeq(M)
    downset = alphaPosetDownsets(M)
    for L in powerset(G):
        idx1 += 1
        idx2 = -1
        for R in powerset(G):
            idx2 += 1
            if L == R:
                mu[idx1,idx2] = 1
            elif leq(L,R):
                s = 0
                for P in downset(R):
                    if P == R:
                        continue
                    s += mu[idx1,powersetSubsetIndex(P,G)]
                mu[idx1,idx2] = -s
    return mu

def nullityVector(M):
    """ (M)

        M __ matroid

        returns the nullity vector of M
    """
    G = sorted(M.groundset())
    nG = len(G)
    nu = Matrix(1,2**nG,sparse=True)
    idx1 = -1
    for L in powerset(G):
        idx1 += 1
        nu[0,idx1] = len(L) - M.rank(L)
    return nu

def alphaVector(M,throughMoebius=False):
    """ (M, throughMoebius=False)

        M __ matroid

        throughMoebius __ determines, whether alpha is calculated from the
                          nullity vector through the moebius-function of alpha_M,
                          or recursively

        returns the alpha vector of M
    """
    if throughMoebius:
        return nullityVector(M) * moebiusMatrixForAlphaPoset(M)
    else:
        G = sorted(M.groundset())
        nG = len(G)
        alpha = Matrix(1,2**nG,sparse=True)
        idx1 = -1
        leq = alphaPosetLeq(M)
        downset = alphaPosetDownsets(M)
        for L in powerset(G):
            idx1 += 1
            aval = len(L) - M.rank(L)
            for R in downset(L):
                if R == L:
                    continue
                aval -= alpha[0,powersetSubsetIndex(R,G)]
            if aval:
                alpha[0,idx1] = aval
        return alpha

def restrictVector(V, G0, G):
    """ (V, G0, G)

        V __ 1 x 2**|G| Matrix
        G0 __ subset of G
        G __ base set of the matrix

        returns the appropriately reduced matrix
    """
    G = sorted(G)
    G0 = sorted(G0)
    V0 = Matrix(1,2**len(G0),sparse=True)
    idx = -1
    for L in powerset(G0):
        idx += 1
        v = V[0,powersetSubsetIndex(L,G)]
        if v:
            V0[0,idx] = v
    return V0


def contractVector(V, e, G):
    """ (V, e, G)
        V __ 1 x 2**|G| Matrix
        e __ element of G
        G __ base set of the matrix

        returns the appropriately reduced matrix
                that consists only of entries corresponding to sets that contain
                e
    """
    G = sorted(G)
    G0 = sorted(set(G).difference([e]))
    V0 = Matrix(1,2**len(G0),sparse=True)
    idx = -1
    for L in powerset(G0):
        idx += 1
        v = V[0,powersetSubsetIndex(frozenset(L).union([e]),G)]
        if v:
            V0[0,idx] = v
    return V0


def restrictMatrix(M, G0, G):
    """
    (M, G0, G)

        M __ 2**|G| x 2**|G| Matrix
        G0 __ subset of G
        G __ base set of the matrix

        returns the appropriately reduced matrix
    """
    G = sorted(G)
    G0 = sorted(G0)
    M0 = Matrix(2**len(G0),2**len(G0),sparse=True)
    idx = -1
    for L in powerset(G0):
        idx += 1
        idx1 = -1
        idxLp = powersetSubsetIndex(L,G)
        for R in powerset(G0):
            idx1 += 1
            v = M[idxLp,powersetSubsetIndex(R,G)]
            if v:
                M0[idx,idx1] = v
    return M0


def deltaAlphaVector(M, C):
    """ (M,C)

        M __ matroid

        C __ minimal elements of a modular cuts


        returns the vector of Delta alpha_M,
                where alpha_N wrt. the extension of M corresponding to C
                restricted to the groundset of M has the property

                alpha_N|(M.groundset) = alpha_M + Delta alpha_M
    """
    G = sorted(M.groundset())
    nG = len(G)
    mu = moebiusMatrixForAlphaPoset(M)
    deltaAlpha = Matrix(1,2**nG,sparse=True)
    FM = frozenset(allFlats(M))
    Cx = set()
    for c in setFamilize(C):
        for F in FM:
            if F.issuperset(c):
                Cx.add(F)
    Cx = frozenset(Cx)
    downset = alphaPosetDownsets(M)
    idx = -1
    for X in powerset(G):
        X = frozenset(X)
        idx += 1
        s = 0
        for Y in downset(X):
            if Y == X:
                continue
            nlty = len(Y) - M.rank(Y)
            for Z in downset(X):
                if not Z in Cx:
                    continue
                if not Y.issubset(Z):
                    continue
                if X == Z:
                    continue
                s += nlty * mu[powersetSubsetIndex(Y,G),powersetSubsetIndex(Z,G)]
        if s:
            deltaAlpha[0,idx] = s
    return deltaAlpha

def powergroundset(M):
    """ (M)

        M __ matroid

        returns powerset(sorted(M.groundset()))
    """
    return powerset(sorted(M.groundset()))


### ---- ###


def calculateAlphaOfExtension(e, C, M, alpha=None, mu=None):
    """ (e, C, M, alpha=None, mu=None)


            e __ name of the new element
            C __ modular cut of the new element (whole cut, not just minimal elts!)
            M __ matroid

            alpha __ alpha vector of M
            mu  __ Möbius function of the alpha_M-poset

        returns the alpha vector of M+e that corresponds to C
    """
    G0 = sorted(M.groundset())
    G1 = sorted(G0+[e])
    if alpha is None:
        alpha = alphaVector(M)
    if mu is None:
        mu = moebiusMatrixForAlphaPoset(M)

    alphaE = Matrix(1,2**len(G1),sparse=True)
    idxE = -1
    deltaAlphaE = {}

    for X in powerset(G1):
        X = frozenset(X)
        idxE += 1
        val = 0
        if e in X:
            X0 = X.difference([e])
            clX0 = M.closure(X0)
            if not clX0 in C:
                if clX0 == X0:
                    val = 0
                else:
                    val = alpha[0,powersetSubsetIndex(X0,G0)]
            else:
                d = 1
                for Z in C:
                    if Z.issubset(X0):
                        if Z == X0:
                            continue
                        #print setStr(Z), "<=", setStr(X0)
                        d -= deltaAlphaE[Z]
                deltaAlphaE[X0] = d
                val = alpha[0,powersetSubsetIndex(X0,G0)] + d
        else:
            s = 0
            for Y in powerset(X):
                Y = frozenset(Y)
                if Y == X:
                    continue
                nuY = len(Y) - M.rank(Y)
                for Z in C:
                    Z = frozenset(Z)
                    if not Y.issubset(Z):
                        continue
                    if not Z.issubset(X):
                        continue
                    if Z == X:
                        continue
                    s += nuY * mu[powersetSubsetIndex(Y,G0),powersetSubsetIndex(Z,G0)]
            val = alpha[0,powersetSubsetIndex(X,G0)] + s # Lemma 2.4.16
        if val:
            alphaE[0,idxE] = val
    return alphaE

#**** FINALLY, SET EXPORT NAMES

__all__ = [x for x in dir() if not (x in __old_dir or x.startswith("_"))]
