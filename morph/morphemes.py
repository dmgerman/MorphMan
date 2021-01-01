# -*- coding: utf-8 -*-
import codecs
import gzip
import os
import pickle as pickle
import sqlite3
import itertools

from abc import ABC, abstractmethod

import re

try:
    import aqt
except:
    pass

# hack: typing is compile time anyway, so, nothing bad happens if it fails, the try is to support anki < 2.1.16
try:
    from aqt.pinnedmodules import typing  # pylint: disable=W0611 # See above hack comment
    from typing import Dict, Set
except ImportError:
    pass


# need some fallbacks if not running from anki and thus morph.util isn't available
try:
    from .util import errorMsg
except ImportError:
    def errorMsg(msg):
        pass

try:
    from .preferences import get_preference as cfg
except:
    def cfg(s):
        return None

def char_set(start, end):
    # type: (str, str) -> set
    return set(chr(c) for c in range(ord(start), ord(end) + 1))


kanji_chars = char_set('㐀', '䶵') | char_set('一', '鿋') | char_set('豈', '頻')


################################################################################
# Lexical analysis
################################################################################

class Morpheme:
    def __init__(self, norm, base, inflected, read, pos, subPos):
        """ Initialize morpheme class.

        POS means part-of-speech.

        Example morpheme infos for the expression "歩いて":

        :param str norm: 歩く [normalized base form]
        :param str base: 歩く
        :param str inflected: 歩い  [mecab cuts off all endings, so there is not て]
        :param str read: アルイ
        :param str pos: 動詞
        :param str subPos: 自立

        """
        # values are created by "mecab" in the order of the parameters and then directly passed into this constructor
        # example of mecab output:    "歩く     歩い    動詞    自立      アルイ"
        # matches to:                 "base     infl    pos     subPos    read"
        self.norm = norm if norm is not None else base
        self.base = base
        self.inflected = inflected
        self.read = read
        self.pos = pos  # type of morpheme determined by mecab tool. for example: u'動詞' or u'助動詞', u'形容詞'
        self.subPos = subPos

    def __setstate__(self, d):
        """ Override default pickle __setstate__ to initialize missing defaults in old databases
        """
        self.norm = d['norm'] if 'norm' in d else d['base']
        self.base = d['base']
        self.inflected = d['inflected']
        self.read = d['read']
        self.pos = d['pos']
        self.subPos = d['subPos']

    def __eq__(self, o):
        return all([isinstance(o, Morpheme), self.norm == o.norm, self.base == o.base, self.inflected == o.inflected,
                    self.read == o.read, self.pos == o.pos, self.subPos == o.subPos,
                    ])

    def __hash__(self):
        return hash((self.norm, self.base, self.inflected, self.read, self.pos, self.subPos))

    def base_kanji(self):
        # type: () -> set
        # todo: profile and maybe cache
        return set(self.base) & kanji_chars

    def getGroupKey(self):
        # type: () -> str

        if cfg('Option_IgnoreGrammarPosition'):
            return '%s\t%s' % (self.norm, self.read)
        else:
            return '%s\t%s\t%s\t' % (self.norm, self.read, self.pos)

    def isProperNoun(self):
        return (self.subPos == '固有名詞' or self.pos == 'PROPN')

    def show(self):  # str
        return '\t'.join([self.norm, self.base, self.inflected, self.read, self.pos, self.subPos])

    def deinflected(self):
        if self.inflected == self.base:
            return self
        else:
            return Morpheme(self.norm, self.base, self.base, self.read, self.pos, self.subPos)


def ms2str(ms):  # [(Morpheme, locs)] -> Str
    return '\n'.join(['%d\t%s' % (len(m[1]), m[0].show()) for m in ms])


class MorphDBUnpickler(pickle.Unpickler):

    def find_class(self, cmodule, cname):
        # Override default class lookup for this module to allow loading databases generated with older
        # versions of the MorphMan add-on.
        if cmodule.endswith('.morph.morphemes'):
            return globals()[cname]
        return pickle.Unpickler.find_class(self, cmodule, cname)

def getMorphemes(morphemizer, expression, note_tags=None):
    expression = replaceBracketContents(expression)

    # go through all replacement rules and search if a rule (which dictates a string to morpheme conversion) can be
    # applied
    replace_rules = cfg('ReplaceRules')
    if note_tags is not None and replace_rules is not None:
        note_tags_set = set(note_tags)
        for (filter_tags, regex, morphemes) in replace_rules:
            if not set(filter_tags) <= note_tags_set:
                continue

            # find matches
            split_expression = re.split(
                regex, expression, maxsplit=1, flags=re.UNICODE)

            if len(split_expression) == 1:
                continue  # no match
            assert (len(split_expression) == 2)

            # make sure this rule doesn't lead to endless recursion
            if len(split_expression[0]) >= len(expression) or len(split_expression[1]) >= len(expression):
                continue

            a_morphs = getMorphemes(
                morphemizer, split_expression[0], note_tags)
            b_morphs = [Morpheme(mstr, mstr, mstr, mstr,
                                 'UNKNOWN', 'UNKNOWN') for mstr in morphemes]
            c_morphs = getMorphemes(
                morphemizer, split_expression[1], note_tags)

            return a_morphs + b_morphs + c_morphs

    ms = morphemizer.getMorphemesFromExpr(expression)

    return ms

square_brackets_regex = re.compile(r'\[[^\]]*\]')
round_brackets_regex = re.compile(r'（[^）]*）')
slim_round_brackets_regexp = re.compile(r'\([^\)]*\)')

def replaceBracketContents(expression):
    if cfg('Option_IgnoreBracketContents'):
        if square_brackets_regex.search(expression):
            expression = square_brackets_regex.sub('', expression)

    if cfg('Option_IgnoreRoundBracketContents'):
        if round_brackets_regex.search(expression):
            expression = round_brackets_regex.sub('', expression)

    if cfg('Option_IgnoreSlimRoundBracketContents'):
        if slim_round_brackets_regexp.search(expression):
            expression = slim_round_brackets_regexp.sub('', expression)

    return expression

################################################################################
# Morpheme db manipulation
################################################################################

class Location(ABC):
    def __init__(self, weight):
        self.weight = weight
        self.maturity = 0

    @abstractmethod
    def show(self):
        pass

    # identifies the class, rather than depend on name __class__
    @abstractmethod 
    def name(self):
        pass


class Nowhere(Location):
    def __init__(self, tag, weight=0):
        super(Nowhere, self).__init__(weight)
        self.tag = tag

    def show(self):
        return '%s@%d' % (self.tag, self.maturity)

    def name(self):
        assert False, "Corpus locations not implemented yet"

class Corpus(Location):
    """A corpus we want to use for priority, without storing more than morpheme frequencies."""

    def __init__(self, name, weight):
        super(Corpus, self).__init__(weight)
        self.name = name

    def show(self):
        return '%s*%s@%d' % (self.name, self.weight, self.maturity)

    def name(self):
        assert False, "Corpus locations not implemented yet"

class TextFile(Location):
    def __init__(self, filePath, lineNo, maturity, weight=1):
        super(TextFile, self).__init__(weight)
        self.filePath = filePath
        self.lineNo = lineNo
        self.maturity = maturity

    def show(self):
        return '%s:%d@%d' % (self.filePath, self.lineNo, self.maturity)

    def name(self):
        return "text-file"

class AnkiDeck(Location):
    """ This maps to/contains information for one note and one relevant field like u'Expression'. """

    def __init__(self, noteId, fieldName, fieldValue, guid, maturity, weight=1):
        super(AnkiDeck, self).__init__(weight)
        self.noteId = noteId
        self.fieldName = fieldName  # for example u'Expression'
        self.fieldValue = fieldValue  # for example u'それだけじゃない'
        self.guid = guid
        # list of intergers, one for every card -> containg the intervals of every card for this note
        self.maturities = None
        self.maturity = maturity
        self.weight = weight

    def show(self):
        return '%d[%s]@%d' % (self.noteId, self.fieldName, self.maturity)

    def name(self):
        return "anki-deck"


def altIncludesMorpheme(m, alt):
    # type: (Morpheme, Morpheme) -> bool

    return m.norm == alt.norm and (m.base == alt.base or m.base_kanji() <= alt.base_kanji())

    
class MorphDb:
    @staticmethod
    def mergeFiles(aPath, bPath, destPath=None,
                   ignoreErrors=False):  # FilePath -> FilePath -> Maybe FilePath -> Maybe Book -> IO MorphDb
        a, b = MorphDb(aPath, ignoreErrors), MorphDb(bPath, ignoreErrors)
        a.merge(b)
        if destPath:
            a.save(destPath)
        return a

    @staticmethod
    def mkFromFile(path, morphemizer, maturity=0):  # FilePath -> Maturity? -> IO Db
        """Returns None and shows error dialog if failed"""
        d = MorphDb()
        try:
            d.importFile(path, morphemizer, maturity=maturity)
        except (UnicodeDecodeError, IOError) as e:
            return errorMsg('Unable to import file. Please verify it is a UTF-8 text file and you have '
                            'permissions.\nFull error:\n%s' % e)
        return d

    def __init__(self, path=None, ignoreErrors=False):  # Maybe Filepath -> m ()
        self.db = {}  # type: Dict[Morpheme, Set[Location]]
        self.groups = {}  # Map NormMorpheme {Set(Morpheme)}
        self.meta = {}
        if path:
            try:
                self.load(path)
            except IOError:
                if not ignoreErrors:
                    raise
        self.analyze()

    # Serialization
    def show(self):  # Str
        s = ''
        for m, ls in self.db.items():
            s += '%s\n' % m.show()
            for l in ls:
                s += '  %s\n' % l.show()
        return s

    def showLocDb(self):  # m Str
        s = ''
        for l, ms in self.locDb().items():
            s += '%s\n' % l.show()
            for m in ms:
                s += '  %s\n' % m.show()
        return s

    def showMs(self):  # Str
        return ms2str(sorted(self.db.items(), key=lambda it: it[0].show()))

    def save(self, path):  # FilePath -> IO ()
        print("\n\nSaving ", path)
        par = os.path.split(path)[0]
        if not os.path.exists(par):
            os.makedirs(par)
        f = gzip.open(path, 'wb')

        data = {'db': self.db,
                'meta': self.meta
                }
        pickle.dump(data, f, -1)
        f.close()
#        if cfg('saveSQLite'):
        save_db(path, self.db.keys(), self.db.items() )

    def print_db(self):
        print("morphs and locations")
        for (m, locs) in self.db.items():
            print(m)
            print(locs)
        print("groups")
        for (g, morphs) in self.groups.items():
            print(g)
            print(morphs)

    def load(self, path):  # FilePath -> m ()
        print("Loading database", path)
        if (True):
            
            (morphs, self.db) = load_db(path)
            print("after Loading database", path)

            # now we need to do the GroupKey
            # TODO rewrite without mutation
            for m in morphs:
                gk = m.getGroupKey()
                if gk not in self.groups:
                    self.groups[gk] = {m}
                else:
                    self.groups[gk].add(m)

            self.print_db()
            return

        f = gzip.open(path)
        try:
            data = MorphDBUnpickler(f).load()
            if 'meta' in data:
                self.meta = data['meta']
                db = data['db']
            else:
                db = data
            for m, locs in db.items():
                self.addMLs1(m, locs)
        except ModuleNotFoundError as e:
            aqt.utils.showInfo(
                "ModuleNotFoundError was thrown. That probably means that you're using database files generated in "
                "the older versions of MorphMan. To fix this issue, please refer to the written guide on database "
                "migration (copy-pasteable link will appear in the next window): "
                "https://gist.github.com/InfiniteRain/1d7ca9ad307c4203397a635b514f00c2")
            raise e
        f.close()

    # Returns True if DB has variations that can match 'm'.
    def matches(self, m):  # Morpheme
        # type: (Morpheme) -> bool
        gk = m.getGroupKey()
        ms = self.groups.get(gk, None)
        if ms is None:
            return False

        # Fuzzy match to variations
        return any(altIncludesMorpheme(m, alt) for alt in ms)

    # Returns set of morph locations that can match 'm'
    def getMatchingLocs(self, m):  # Morpheme
        # type: (Morpheme) -> Set[Location]
        locs = set()
        gk = m.getGroupKey()
        ms = self.groups.get(gk, None)
        if ms is None:
            return locs

        # Fuzzy match to variations
        for variation in ms:
            if altIncludesMorpheme(m, variation):
                locs.update(self.db[variation])
        return locs

    # Adding
    def clear(self):  # m ()
        self.db = {}
        self.groups = {}
        self.meta = {}

    def addMLs(self, mls):  # [ (Morpheme,Location) ] -> m ()
        for m, loc in mls:
            if m in self.db:
                self.db[m].add(loc)
            else:
                self.db[m] = {loc}
                gk = m.getGroupKey()
                if gk not in self.groups:
                    self.groups[gk] = {m}
                else:
                    self.groups[gk].add(m)

    def addMLs1(self, m, locs):  # Morpheme -> {Location} -> m ()
        if m in self.db:
            self.db[m].update(locs)
        else:
            self.db[m] = set(locs)
            gk = m.getGroupKey()
            if gk not in self.groups:
                self.groups[gk] = {m}
            else:
                self.groups[gk].add(m)

    def addMsL(self, ms, loc):  # [Morpheme] -> Location -> m ()
        self.addMLs((m, loc) for m in ms)

    def addFromLocDb(self, ldb):  # Map Location {Morpheme} -> m ()
        for l, ms in ldb.items():
            self.addMLs([(m, l) for m in ms])

    def removeMorphs(self, iter):
        for m in iter:
            if m in self.db:
                self.db.pop(m)
                gk = m.getGroupKey()
                if gk in self.groups:
                    self.groups[gk].remove(m)

    # returns number of added entries
    def merge(self, md):  # Db -> m Int
        new = 0
        for m, locs in md.db.items():
            if m in self.db:
                new += len(locs - self.db[m])
                self.db[m].update(locs)
            else:
                new += len(locs)
                self.addMLs1(m, locs)

        return new

    # FilePath -> Morphemizer -> Maturity? -> IO ()
    def importFile(self, path, morphemizer, maturity=0):
        f = codecs.open(path, encoding='utf-8')
        inp = f.readlines()
        f.close()

        for i, line in enumerate(inp):
            ms = getMorphemes(morphemizer, line.strip())
            self.addMLs((m, TextFile(path, i + 1, maturity)) for m in ms)

    # Analysis (local)
    def frequency(self, m):  # Morpheme -> Int
        return sum(getattr(loc, 'weight', 1) for loc in self.getMatchingLocs(m))

    # Analysis (global)
    def locDb(self, recalc=True):  # Maybe Bool -> m Map Location {Morpheme}
        # type: (bool) ->  Dict[Location, Set[Morpheme]]
        if hasattr(self, '_locDb') and not recalc:
            return self._locDb  # pylint: disable=E0203 # pylint is wrong
        self._locDb = d = {}  # type: Dict[Location, Set[Morpheme]]
        for m, ls in self.db.items():
            for l in ls:
                if l in d:
                    d[l].add(m)
                else:
                    d[l] = {m}
        return d

    def fidDb(self, recalc=True):  # Maybe Bool -> m Map FactId Location
        if hasattr(self, '_fidDb') and not recalc:
            return self._fidDb  # pylint: disable=E0203 # pylint is wrong
        self._fidDb = d = {}
        for loc in self.locDb():
            try:
                d[(loc.noteId, loc.guid, loc.fieldName)] = loc
            except AttributeError:
                pass  # location isn't an anki fact
        return d

    def countByType(self):  # Map Pos Int
        d = {}
        for m in self.db.keys():
            d[m.pos] = d.get(m.pos, 0) + 1
        return d

    def analyze(self):  # m ()
        self.posBreakdown = self.countByType()
        self.kCount = len(self.groups)
        self.vCount = len(self.db)

    def analyze2str(self):  # m Str
        self.analyze()
        posStr = '\n'.join('%d\t%d%%\t%s' % (v, 100. * v / self.vCount, k)
                           for k, v in self.posBreakdown.items())
        return 'Total normalized morphemes: %d\nTotal variations: %d\nBy part of speech:\n%s' % (
            self.kCount, self.vCount, posStr)


# sqlite code

def connect_db(path):
    conn = sqlite3.connect(path)
    return conn

def drop_table(cur, name):
    sql = "drop table if exists %s;"%(name)
    cur.execute(sql)

def create_table(cur, name, fields, extra = ""):
    sql = "create table %s (%s%s);"%(name,fields, extra)
    cur.execute(sql)

# helper functions to convert morphman objectsi into sql tuples
def transcode_morph(item):
    return (item.norm, item.base, item.inflected, item.read, item.pos, item.subPos)

    
def save_db_all_morphs(cur, morph_to_id, tname='morphs'):

    # morph_to_id is a dictionary of morphs to id

    # fields  of table to be created
    fields = "morphid, norm, base, inflected, read, pos, subpos"

    drop_table(cur, tname)

    create_table(cur, tname,fields, ", primary key (morphid)")

    def transcode_item_pair(el):
        # el is a pair: <morph object, int>
        # this is a helper function for the map below
        item = el[0]
        return (el[1],)+ transcode_morph(item)

    # convert the info in the dict of morphs into list of tuples
    tuples = map(transcode_item_pair, morph_to_id.items())

    # insert them all at once
    cur.executemany("INSERT INTO %s (%s) VALUES(?,?,?,?,?,?,?);"%(tname,fields), tuples)

def read_db_all_morphs(cur):
    # read the morphs as a dictionary, where the key is the morph tuple and
    # the value is the morphid
    # see save_db_all_morphs for the schema of the morphs relation
    
    cur.execute("SELECT * FROM morphs;")
    rows = cur.fetchall()
    forDict = map(lambda x: (x[1:], x[0]), rows)
    return dict(forDict)

def morph_locations_to_tuples(morphWithLocations, morph_to_id, f_transcode, loc_name):
    # morphWithLocations is a pair of morph and locations
    # we need to return a list of tuples (morphid, location info...)
    morph, locs = morphWithLocations
    return list(map(lambda y: (morph_to_id[morph],) +f_transcode(y),
                    filter(lambda x: x.name()== loc_name ,locs)))

def convert_locations_to_tuples(locations, morph_to_id, f_transcode, tag):

    # we need to convert the db of morphs into a list of tuples
    # where the first value is the morphid

    # but only if the location has certain tag
    
    # each location is a pair: morph, list of locations

    # f_transcode is the function to convert the attributes of the location
    # to a tuple. the morphid is spliced first into this tuple

    
    locationsLists =map(lambda x: # x is a pair of morph and list of locations
                        morph_locations_to_tuples(x, morph_to_id, f_transcode, tag),
                        locations)

    # flatten the list... because we have a list of tuples (one list per morph)
    # note that this list might be empty
    return [val for sublist in locationsLists for val in sublist]


def save_db_anki_locations(cur, locations, morph_to_id, tname='ankilocs'):
    #
    # save the locations of type anki-deck to given table
    #
    # morph_to_id is a dictionary that maps a morph class to its integer
    # as stored in the database
    #
    # fields for the table
    fields = "morphid, noteid, field, fieldvalue, guid, maturity, weight"

    # convert to a db tuple
    def transcode_anki_location(loc):
        return (loc.noteId, loc.fieldName, loc.fieldValue, loc.maturity, loc.guid, loc.weight)

    # it is usually faster to drop the table than delete/update the tuples
    # in it

    drop_table(cur, tname)
    create_table(cur, tname, fields,
                 ", primary key (morphid, noteid, field), foreign key (morphid) references morphs")

    tuples = convert_locations_to_tuples(locations,
                                         morph_to_id,
                                         transcode_anki_location,
                                         'anki-deck')

    if len(tuples) > 0:
        cur.executemany("INSERT INTO %s (%s) VALUES(?,?,?,?,?,?,?);"%(tname,fields), tuples)


def save_db_text_file_locations(cur, locations, morph_to_id, tname='filelocs'):
    #
    # save the locations of type text-file to given table
    #
    # morph_to_id is a dictionary that maps a morph class to its integer
    # as stored in the database


    # fields for the table
    fields = "morphid, filename, line, maturity"

    # it is usually faster to drop the table than delete/update the tuples
    # in it

    drop_table(cur, tname)
    create_table(cur, tname, fields,
                 ", foreign key (morphid) references morphs")

    # convert to a db tuple
    def transcode_text_file_location(loc):
        return (loc.filePath, loc.lineNo, loc.maturity)

    tuples = convert_locations_to_tuples(locations,
                                         morph_to_id,
                                         transcode_text_file_location,
                                         'text-file')


    if len(tuples) > 0:
        cur.executemany("INSERT INTO %s (%s) VALUES(?,?,?,?);"%(tname,fields), tuples)
    
def save_db_locations(cur, locations, morph_to_id):

    # unfortunately, a morph might include different types of locations
    # so we need to scan each type once
    # functions below only save their corresponding type

    save_db_anki_locations(cur, locations, morph_to_id)

    save_db_text_file_locations(cur, locations, morph_to_id)



        
def save_db_files(cur, files):
    tname = 'files'
    # save a morphman db as a table in database
    #
    # morph_to_id is a dictionary that maps a morph class to its integer
    # as stored in the database
    #
    # fields for the table
    fields = "fileidx, filename, filetype"

    # it is usually faster to drop the table than delete/update the tuples
    # in it

    drop_table(cur, tname)
    create_table(cur, tname, fields,
                 ", primary key(fileidx)"
                 )

    # the list of files is in order, add an integer identifier
    tuples = list(map(lambda file:
                 (file[0], file[1][0], file[1][1]),
                 enumerate(files)))
    print(tuples)

    cur.executemany("INSERT INTO %s (%s) VALUES(?,?,?);"%(tname,fields), tuples)
        


def save_db_lines(cur, fileidx, lines, do_create_table= False):
    tname = 'lines'
    # save a morphman db as a table in database
    #
    # morph_to_id is a dictionary that maps a morph class to its integer
    # as stored in the database
    #
    # fields for the table
    fields = "fileidx, line, position, morphid"

    # it is usually faster to drop the table than delete/update the tuples
    # in it
    if do_create_table:
        drop_table(cur, tname)
        create_table(cur, tname, fields,
                     ", foreign key (fileidx) references files")

    def convert_each_line(lineno, morphs):
        result = list(map(lambda m: [fileidx, lineno, m[0], m[1]], enumerate(morphs)))
        return result
        
    linesLists = map(lambda line:
                    convert_each_line(line[0], list(line[1])),
                     zip(itertools.count(1), lines))

    # flatten the list... because we have a list of lists (one list per morph)
    tuples = [val for sublist in linesLists for val in sublist]

    cur.executemany("INSERT INTO %s (%s) VALUES(?,?,?,?);"%(tname,fields), tuples)
        
def save_db_morph_counts(cur, fileidx, counts, do_create_table= False):

    tname = 'morph_counts'
    # fields for the table
    fields = "fileidx, morphid, nmorphs"

    # it is usually faster to drop the table than delete/update the tuples
    # in it
    if do_create_table:
        drop_table(cur, tname)
        create_table(cur, tname, fields,
                     ", foreign key (fileidx) references files")

    # convert to a list of tuples, adding the file index

    tuples = map(lambda count: (fileidx, count[0], count[1]), counts.items())

    cur.executemany("INSERT INTO %s (%s) VALUES(?,?,?);"%(tname,fields), tuples)
        


def save_db(path, morphs, locations):
    # assume that the directory is already created...
    # exceptions will handle the errors

    # we need to wedge this code in here, while we refactor the code...
    # morphman stores info in a bunch of files.
    #
    # database with each "file" as a table
    # so let use the basefilename of the relation as

    dbName = path + ".sqlite"

    conn = connect_db(dbName)
    with conn:
        cur = conn.cursor()
        # it looks like we only need to save the "all" data
        # the others seem to be subsets of it (based on the
        # maturity field)

        # add an unique int to identify the morph in the database
        # assumes that all morphs are unique
        # create a dictionary to add this 'key' to the locations

        morph_to_id = dict(zip(morphs, itertools.count()))
           
        save_db_all_morphs(cur, morph_to_id)
        # then we need to save the locations
        # every morph in location is guaranteed in db at this point
            
        save_db_locations(cur, locations, morph_to_id)
        conn.commit()

    print("Saved to sqlite dbname [%s]"%(dbName))

def convert_tuples_to_morph_locations(cur, query, tuples_to_morph_locations):
    # the query results has to be grouped by because we must need to have a set
    # locations for each morph
    iter_per_morph_loc = itertools.groupby(cur.execute(query), lambda x: x[0])

    morphs_with_loc = dict(map(tuples_to_morph_locations,
                      [list(v) for k,v in iter_per_morph_loc]))

    return morphs_with_loc
            

def read_db_anki_locations(cur, mid_to_morph_dict, tname='ankilocs'):
    # read the locations and return a dictionary that maps the
    # morph (object) to the location
    fields = "morphid, noteid, field, fieldvalue, guid, maturity, weight"
    query = '''
select %s from %s
order by morphid, noteid, field
'''%(fields, tname)

    def tuples_to_morph_locations(tuples):
        # tuples is an iterator
        tuples = list(tuples)
        assert len(tuples)>0, "There should be at least one tuple here"
        mid = tuples[0][0]
        # check the values
        for t in tuples:
            assert t[0] == mid, "mid in list of tuples should match"
        print("------------------------------------")
        print(tuples)
        # create set of locations
        locs = set(map(lambda x: AnkiDeck(x[1],x[2],x[3],x[4],x[5],x[6]), tuples))
        print("done with tuples")
        return (mid_to_morph_dict[mid], locs)

    return convert_tuples_to_morph_locations(cur, query, tuples_to_morph_locations)


def read_db_text_file_locations(cur, mid_to_morph_dict, tname='filelocs'):
    # read the locations and return a dictionary that maps the
    # morph (object) to the location
    fields = "morphid, filename, line, maturity"
                
    query = '''
select %s from %s order by morphid, filename, line
'''%(fields, tname)

    def tuples_to_morph_locations(tuples):
        # tuples is an iterator
        tuples = list(tuples)
        assert len(tuples)>0, "There should be at least one tuple here"
        mid = tuples[0][0]
        # check the values
        for t in tuples:
            assert t[0] == mid, "mid in list of tuples should match"
        print("------------------------------------")
        print(tuples)
        # create set of locations
        locs = set(map(lambda x: TextFile(x[1],x[2],x[3]), tuples))
        print("done with tuples")
        return (mid_to_morph_dict[mid], locs)

    return convert_tuples_to_morph_locations(cur, query, tuples_to_morph_locations)


def read_db_all_morphs_as_dict(cur, tname):

    def create_morph(m):
        return Morpheme(m[0],m[1],m[2],m[3],m[4],m[5])

    query = 'SELECT morphid, norm, base, inflected, read, pos, subpos FROM ' + tname
    
    return dict(map(lambda x: (x[0], create_morph(x[1:])), cur.execute(query)))

def merge_locs_dict(a, b):
    emptySet = set()
    return dict([ (x, a.get(x, emptySet).union(b.get(x, emptySet)))
                  for x in set(a.keys()) | set(b.keys()) ])

def load_db(path):

    # returns (morphs, locations)
    # it ends with .db so cut it
    assert path.endswith('.sqlite'), "extension is no longer .db?"

    # name of the morphs to save (all, known, etc.)

    print("reading from db", path)

    conn = connect_db(path)
    with conn:
        cur = conn.cursor()

        # we need to load
        #    all
        #
        # and split them into
        #    known
        #    mature
        print("reading morphs")
        mid_to_morph_dict = read_db_all_morphs_as_dict(cur, 'morphs')
            
        print("reading morphs done")

        # read a list of all the locations
        # returns a dictionary: morph object -> location object

        anki_locs_dict = read_db_anki_locations(cur, mid_to_morph_dict)
        print("reading anki locs done")

        text_file_locs_dict = read_db_text_file_locations(cur, mid_to_morph_dict)
        print("reading text locs done")

        merged = merge_locs_dict(anki_locs_dict, text_file_locs_dict)
        print("merged locs")


    return(mid_to_morph_dict.values(), merged)


def read_db_all_morph_counts_iter_per_file_ordered(cur):
    query ='''
    SELECT fileidx, morphid, nmorphs from morph_counts
              order by fileidx
'''    
    return itertools.groupby(cur.execute(query),
                             lambda x: x[0])


def read_db_all_lines_iter_per_file_ordered(cur):
    query = 'SELECT fileidx, line, position, morphid from lines order by fileidx, line, position'
    
    return itertools.groupby(cur.execute(query),
                             lambda x: x[0])


def read_db_get_filename_by_index(cur, fileidx):
    
    query = 'SELECT filename from files where fileidx = %d'%fileidx
    cur.execute(query)
    result = cur.fetchone()
    return None if result == None else result[0]

def read_db_table_exists(cur, tname):
    query = "SELECT name FROM sqlite_master WHERE type='table' AND name=?"
    cur.execute(query, (tname,))
    result = cur.fetchall()
    return len(result) > 0

def read_db_has_locations_table(cur):
    return read_db_table_exists(cur, 'lines')

