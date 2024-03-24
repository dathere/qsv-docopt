// I am overall pretty displeased with the quality of code in this module.
// I wrote it while simultaneously trying to build a mental model of Docopt's
// specification (hint: one does not exist in written form). As a result, there
// is a lot of coupling and some duplication.
//
// Some things that I think are good about the following code:
//
//   - The representation of a "usage pattern." I think it is a minimal representation of a
//     pattern's syntax. (One possible tweak: `Optional<Vec<Pattern>>` -> `Optional<Box<Pattern>>`.)
//   - Some disciplined use of regexes. I use a pretty basic state machine for parsing patterns, but
//     for teasing out the patterns and options from the Docopt string and for picking out flags
//     with arguments, I think regexes aren't too bad. There may be one or two scary ones though.
//   - The core matching algorithm is reasonably simple and concise, but I think writing down some
//     contracts will help me figure out how to make the code clearer.
//
// Some bad things:
//
//   - I tried several times to split some of the pieces in this module into separate modules. I
//     could find no clear separation. This suggests that there is too much coupling between parsing
//     components. I'm not convinced that the coupling is necessary.
//   - The parsers for patterns and argv share some structure. There may be an easy abstraction
//     waiting there.
//   - It is not efficient in the slightest. I tried to be conservative with copying strings, but I
//     think I failed. (It may not be worthwhile to fix this if it makes the code more awkward.
//     Docopt does not need to be efficient.)
//
// Some things to do immediately:
//
//   - Document representation and invariants.
//   - Less important: write contracts for functions.
//
// Long term:
//
//   - Write a specification for Docopt.

use std::{
    cmp::Ordering,
    collections::hash_map::Entry::{Occupied, Vacant},
    fmt,
};

use ahash::{AHashMap, AHashSet};
use regex::Regex;
use strsim::levenshtein;

use self::{
    Argument::{One, Zero},
    Atom::{Command, Long, Positional, Short},
    Pattern::{Alternates, Optional, PatAtom, Repeat, Sequence},
};
use crate::{
    cap_or_empty,
    dopt::Value::{self, Counted, List, Plain, Switch},
    synonym::SynonymMap,
};

macro_rules! err(
    ($($arg:tt)*) => (return Err(format!($($arg)*)))
);

#[derive(Clone)]
pub struct Parser {
    pub program:     String,
    pub full_doc:    String,
    pub usage:       String,
    pub descs:       SynonymMap<Atom, Options>,
    usages:          Vec<Pattern>,
    last_atom_added: Option<Atom>, // context for [default: ...]
}

impl Parser {
    pub fn new(doc: &str) -> Result<Parser, String> {
        let mut d = Parser {
            program:         String::new(),
            full_doc:        doc.into(),
            usage:           String::new(),
            usages:          vec![],
            descs:           SynonymMap::new(),
            last_atom_added: None,
        };
        d.parse(doc)?;
        Ok(d)
    }

    pub fn matches(&self, argv: &Argv<'_>) -> Option<SynonymMap<String, Value>> {
        for usage in &self.usages {
            match Matcher::matches(argv, usage) {
                None => continue,
                Some(vals) => return Some(vals),
            }
        }
        None
    }

    pub fn parse_argv(&self, argv: &[String], options_first: bool) -> Result<Argv<'_>, String> {
        Argv::new(self, argv, options_first)
    }
}

impl Parser {
    fn options_atoms(&self) -> Vec<Atom> {
        let mut atoms = vec![];
        for (atom, _) in self.descs.iter().filter(|&(_, opts)| opts.is_desc) {
            atoms.push(atom.clone());
        }
        atoms
    }

    fn has_arg(&self, atom: &Atom) -> bool {
        match self.descs.find(atom) {
            None => false,
            Some(opts) => opts.arg.has_arg(),
        }
    }

    fn has_repeat(&self, atom: &Atom) -> bool {
        match self.descs.find(atom) {
            None => false,
            Some(opts) => opts.repeats,
        }
    }

    fn parse(&mut self, doc: &str) -> Result<(), String> {
        decl_regex! {
            MUSAGE: r"(?s)(?i:usage):\s*(?P<prog>\S+)(?P<pats>.*?)(?:$|\n\s*\n)";
        }
        let caps = match MUSAGE.captures(doc) {
            None => err!("Could not find usage patterns in doc string."),
            Some(caps) => caps,
        };

        let prog = cap_or_empty(&caps, "prog");
        if prog.is_empty() {
            err!("Could not find program name in doc string.")
        }

        prog.clone_into(&mut self.program);
        caps.get(0).unwrap().as_str().clone_into(&mut self.usage);

        // Before we parse the usage patterns, we look for option descriptions.
        // We do this because the information in option descriptions can be
        // used to resolve ambiguities in usage patterns (i.e., whether
        // `--flag ARG` is a flag with an argument or not).
        //
        // From the docopt page, "every" line starting with a `-` or a `--`
        // is considered an option description. Instead, we restrict the lines
        // to any line *not* in the usage pattern section.
        //
        // *sigh* Apparently the above is not true. The official test suite
        // includes `Options: -a ...`, which means some lines not beginning
        // with `-` can actually have options.
        let (pstart, pend) = caps.get(0).map(|m| (m.start(), m.end())).unwrap();
        let (before, after) = (&doc[..pstart], &doc[pend..]);
        // We process every line here (instead of restricting to lines starting
        // with "-") because we need to check every line for a default value.
        // The default value always belongs to the most recently defined desc.
        for line in before.lines().chain(after.lines()) {
            self.parse_desc(line)?;
        }

        let mprog = format!("^(?:{})?\\s*(.*?)\\s*$", regex::escape(prog));
        let pats = Regex::new(&mprog).unwrap();

        let pats_str = cap_or_empty(&caps, "pats");
        if pats_str.is_empty() {
            let pattern = PatParser::new(self, "").parse()?;
            self.usages.push(pattern);
        } else {
            for line in pats_str.lines() {
                for pat in pats.captures_iter(line.trim()) {
                    let pattern = PatParser::new(self, &pat[1]).parse()?;
                    self.usages.push(pattern);
                }
            }
        }
        Ok(())
    }

    fn parse_desc(&mut self, full_desc: &str) -> Result<(), String> {
        decl_regex! {
            OPTIONS:r"^\s*(?i:options:)\s*";
            ISFLAG: r"^(-\S|--\S)";
            REMOVE_DESC: r"  .*$";
            NORMALIZE_FLAGS: r"([^-\s]), -";
            FIND_FLAGS:
                r"(?x)
                (?:(?P<long>--[^\x20\t=]+)|(?P<short>-[^\x20\t=]+))
                (?:(?:\x20|=)(?P<arg>[^.-]\S*))?
                (?P<repeated>\x20\.\.\.)?";
        }
        let desc = OPTIONS.replace(full_desc.trim(), "");
        let desc = &*desc;
        if !ISFLAG.is_match(desc) {
            self.parse_default(full_desc)?;
            return Ok(());
        }

        // Get rid of the description, which must be at least two spaces
        // after the flag or argument.
        let desc = REMOVE_DESC.replace(desc, "");
        // Normalize `-x, --xyz` to `-x --xyz`.
        let desc = NORMALIZE_FLAGS.replace(&desc, "$1 -");
        let desc = desc.trim();

        let (mut short, mut long) = <(String, String)>::default();
        let mut has_arg = false;
        let mut last_end = 0;
        let mut repeated = false;
        for flags in FIND_FLAGS.captures_iter(desc) {
            last_end = flags.get(0).unwrap().end();
            if !cap_or_empty(&flags, "repeated").is_empty() {
                // If the "repeated" subcapture is not empty, then we have
                // a valid repeated option.
                repeated = true;
            }
            let (s, l) = (cap_or_empty(&flags, "short"), cap_or_empty(&flags, "long"));
            if !s.is_empty() {
                if !short.is_empty() {
                    err!(
                        "Only one short flag is allowed in an option description, but found \
                         '{short}' and '{s}'."
                    )
                }
                short = s.into();
            }
            if !l.is_empty() {
                if !long.is_empty() {
                    err!(
                        "Only one long flag is allowed in an option description, but found \
                         '{long}' and '{l}'."
                    )
                }
                long = l.into();
            }
            if let Some(arg) = flags.name("arg").map(|m| m.as_str()) {
                if !arg.is_empty() {
                    if !Atom::is_arg(arg) {
                        err!("Argument '{arg}' is not of the form ARG or <arg>.")
                    }
                    has_arg = true; // may be changed to default later
                }
            }
        }
        // Make sure that we consumed everything. If there are leftovers,
        // then there is some malformed description. Alert the user.
        assert!(last_end <= desc.len());
        if last_end < desc.len() {
            err!(
                "Extraneous text '{}' in option description '{desc}'.",
                &desc[last_end..]
            )
        }
        self.add_desc(&short, &long, has_arg, repeated);
        // Looking for default in this line must come after adding the
        // description, otherwise `parse_default` won't know which option
        // to assign it to.
        self.parse_default(full_desc)
    }

    fn parse_default(&mut self, desc: &str) -> Result<(), String> {
        decl_regex! {
            FIND_DEFAULT: r"\[(?i:default):(?P<val>.*)\]";
        }
        let defval = match FIND_DEFAULT.captures(desc) {
            None => return Ok(()),
            Some(c) => cap_or_empty(&c, "val").trim(),
        };
        let last_atom = match self.last_atom_added {
            None => {
                err!("Found default value '{defval}' in '{desc}' before first option description.")
            }
            Some(ref atom) => atom,
        };
        let opts = self
            .descs
            .find_mut(last_atom)
            .unwrap_or_else(|| panic!("BUG: last opt desc key ('{last_atom:?}') is invalid."));
        match opts.arg {
            One(None) => {} // OK
            Zero => err!(
                "Cannot assign default value '{defval}' to flag '{last_atom}' that has no \
                 arguments."
            ),
            One(Some(ref curval)) => err!(
                "Flag '{last_atom}' already has a default value of '{curval}' (second default \
                 value: '{defval}')."
            ),
        }
        opts.arg = One(Some(defval.into()));
        Ok(())
    }

    fn add_desc(&mut self, short: &str, long: &str, has_arg: bool, repeated: bool) {
        assert!(!short.is_empty() || !long.is_empty());
        if !short.is_empty() && short.chars().count() != 2 {
            // It looks like the reference implementation just ignores
            // these lines.
            return;
        }
        let mut opts = Options::new(repeated, if has_arg { One(None) } else { Zero });
        opts.is_desc = true;

        if !short.is_empty() && !long.is_empty() {
            let (short, long) = (Atom::new(short), Atom::new(long));
            self.descs.insert(long.clone(), opts);
            self.descs.insert_synonym(short, long.clone());
            self.last_atom_added = Some(long);
        } else if !short.is_empty() {
            let short = Atom::new(short);
            self.descs.insert(short.clone(), opts);
            self.last_atom_added = Some(short);
        } else if !long.is_empty() {
            let long = Atom::new(long);
            self.descs.insert(long.clone(), opts);
            self.last_atom_added = Some(long);
        }
    }
}

impl fmt::Debug for Parser {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fn sorted<T: Ord>(mut xs: Vec<T>) -> Vec<T> {
            xs.sort();
            xs
        }

        writeln!(f, "=====")?;
        writeln!(f, "Program: {}", self.program)?;

        writeln!(f, "Option descriptions:")?;
        let keys = sorted(self.descs.keys().collect());
        for &k in &keys {
            writeln!(f, "  '{k}' => {:?}", self.descs.get(k))?;
        }

        writeln!(f, "Synonyms:")?;
        let keys: Vec<(&Atom, &Atom)> = sorted(self.descs.synonyms().collect());
        for &(from, to) in &keys {
            writeln!(f, "  {from:?} => {to:?}")?;
        }

        writeln!(f, "Usages:")?;
        for pat in &self.usages {
            writeln!(f, "  {pat:?}")?;
        }
        writeln!(f, "=====")
    }
}

struct PatParser<'a> {
    dopt:      &'a mut Parser,
    tokens:    Vec<String>, // used while parsing a single usage pattern
    curi:      usize,       // ^^ index into pattern chars
    expecting: Vec<char>,   // stack of expected ']' or ')'
}

impl<'a> PatParser<'a> {
    fn new(dopt: &'a mut Parser, pat: &str) -> PatParser<'a> {
        PatParser {
            dopt,
            tokens: pattern_tokens(pat),
            curi: 0,
            expecting: vec![],
        }
    }

    fn parse(&mut self) -> Result<Pattern, String> {
        // let mut seen = HashSet::new();
        let mut p = self.pattern()?;
        match self.expecting.pop() {
            None => {}
            Some(c) => err!("Unclosed group. Expected '{c}'."),
        }
        p.add_options_shortcut(self.dopt);
        p.tag_repeats(&mut self.dopt.descs);
        Ok(p)
    }

    fn pattern(&mut self) -> Result<Pattern, String> {
        let mut alts = vec![];
        let mut seq = vec![];
        while !self.is_eof() {
            match self.cur() {
                "..." => {
                    err!("'...' must appear directly after a group, argument, flag or command.")
                }
                "-" | "--" => {
                    // As per specification, `-` and `--` by themselves are
                    // just commands that should be interpreted conventionally.
                    seq.push(self.command());
                }
                "|" => {
                    if seq.is_empty() {
                        err!("Unexpected '|'. Not in form 'a | b | c'.")
                    }
                    self.next_noeof("pattern")?;
                    alts.push(Sequence(seq));
                    seq = vec![];
                }
                "]" | ")" => {
                    if seq.is_empty() {
                        err!("Unexpected '{}'. Empty groups are not allowed.", self.cur())
                    }
                    match self.expecting.pop() {
                        None => err!("Unexpected '{}'. No open bracket found.", self.cur()),
                        Some(c) => {
                            if c != self.cur().chars().next().unwrap() {
                                err!("Expected '{c}' but got '{}'.", self.cur())
                            }
                        }
                    }
                    let mk: fn(Vec<Pattern>) -> Pattern = if self.cur() == "]" {
                        Optional
                    } else {
                        Sequence
                    };
                    self.next();
                    return if alts.is_empty() {
                        Ok(mk(seq))
                    } else {
                        alts.push(Sequence(seq));
                        Ok(mk(vec![Alternates(alts)]))
                    };
                }
                "[" => {
                    // Check for special '[options]' shortcut.
                    if self.atis(1, "options") && self.atis(2, "]") {
                        self.next(); // cur == options
                        self.next(); // cur == ]
                        self.next();
                        seq.push(self.maybe_repeat(Optional(vec![])));
                        continue;
                    }
                    self.expecting.push(']');
                    seq.push(self.group()?);
                }
                "(" => {
                    self.expecting.push(')');
                    seq.push(self.group()?);
                }
                _ => {
                    if Atom::is_short(self.cur()) {
                        seq.extend(self.flag_short()?);
                    } else if Atom::is_long(self.cur()) {
                        seq.push(self.flag_long()?);
                    } else if Atom::is_arg(self.cur()) {
                        // These are always positional.
                        // Arguments for -s and --short are picked up
                        // when parsing flags.
                        seq.push(self.positional());
                    } else if Atom::is_cmd(self.cur()) {
                        seq.push(self.command());
                    } else {
                        err!("Unknown token type '{}'.", self.cur())
                    }
                }
            }
        }
        if alts.is_empty() {
            Ok(Sequence(seq))
        } else {
            alts.push(Sequence(seq));
            Ok(Alternates(alts))
        }
    }

    fn flag_short(&mut self) -> Result<Vec<Pattern>, String> {
        let mut seq = vec![];
        let stacked: String = self.cur()[1..].into();
        for (i, c) in stacked.chars().enumerate() {
            let atom = self.dopt.descs.resolve(&Short(c));
            let mut pat = PatAtom(atom.clone());
            if self.dopt.has_repeat(&atom) {
                pat = Pattern::repeat(pat);
            }
            seq.push(pat);

            // The only way for a short option to have an argument is if
            // it's specified in an option description.
            if self.dopt.has_arg(&atom) {
                // At this point, the flag MUST have an argument. Therefore,
                // we interpret the "rest" of the characters as the argument.
                // If the "rest" is empty, then we peek to find and make sure
                // there is an argument.
                let rest = &stacked[i + 1..];
                if rest.is_empty() {
                    self.next_flag_arg(&atom)?;
                } else {
                    self.errif_invalid_flag_arg(&atom, rest)?;
                }
                // We either error'd or consumed the rest of the short stack as
                // an argument.
                break;
            }
            self.add_atom_ifnotexists(Zero, &atom);
        }
        self.next();
        // This is a little weird. We've got to manually look for a repeat
        // operator right after the stack, and then apply it to each short
        // flag we generated.
        // If "sequences" never altered semantics, then we could just use that
        // here to group a short stack.
        if self.atis(0, "...") {
            self.next();
            seq = seq.into_iter().map(Pattern::repeat).collect();
        }
        Ok(seq)
    }

    fn flag_long(&mut self) -> Result<Pattern, String> {
        let (atom, arg) = parse_long_equal(self.cur())?;
        let atom = self.dopt.descs.resolve(&atom);
        if self.dopt.descs.contains_key(&atom) {
            // Options already exist for this atom, so we must check to make
            // sure things are consistent.
            let has_arg = self.dopt.has_arg(&atom);
            if arg.has_arg() && !has_arg {
                // Found `=` in usage, but previous usage of this flag
                // didn't specify an argument.
                err!("Flag '{atom}' does not take any arguments.")
            } else if !arg.has_arg() && has_arg {
                // Didn't find any `=` in usage for this flag, but previous
                // usage of this flag specifies an argument.
                // So look for `--flag ARG`
                self.next_flag_arg(&atom)?;
                // We don't care about the value of `arg` since options
                // already exist. (In which case, the argument value can never
                // change.)
            }
        }
        self.add_atom_ifnotexists(arg, &atom);
        self.next();
        let pat = if self.dopt.has_repeat(&atom) {
            Pattern::repeat(PatAtom(atom))
        } else {
            PatAtom(atom)
        };
        Ok(self.maybe_repeat(pat))
    }

    fn next_flag_arg(&mut self, atom: &Atom) -> Result<(), String> {
        self.next_noeof(&format!("argument for flag '{atom}'"))?;
        self.errif_invalid_flag_arg(atom, self.cur())
    }

    fn errif_invalid_flag_arg(&self, atom: &Atom, arg: &str) -> Result<(), String> {
        if !Atom::is_arg(arg) {
            err!("Expected argument for flag '{atom}', but found malformed argument '{arg}'.")
        }
        Ok(())
    }

    fn command(&mut self) -> Pattern {
        let atom = Atom::new(self.cur());
        self.add_atom_ifnotexists(Zero, &atom);
        self.next();
        self.maybe_repeat(PatAtom(atom))
    }

    fn positional(&mut self) -> Pattern {
        let atom = Atom::new(self.cur());
        self.add_atom_ifnotexists(Zero, &atom);
        self.next();
        self.maybe_repeat(PatAtom(atom))
    }

    fn add_atom_ifnotexists(&mut self, arg: Argument, atom: &Atom) {
        if !self.dopt.descs.contains_key(atom) {
            let opts = Options::new(false, arg);
            self.dopt.descs.insert(atom.clone(), opts);
        }
    }

    fn group(&mut self) -> Result<Pattern, String> {
        self.next_noeof("pattern")?;
        let pat = self.pattern()?;
        Ok(self.maybe_repeat(pat))
    }

    fn maybe_repeat(&mut self, pat: Pattern) -> Pattern {
        if self.atis(0, "...") {
            self.next();
            Pattern::repeat(pat)
        } else {
            pat
        }
    }

    fn is_eof(&self) -> bool {
        self.curi == self.tokens.len()
    }
    fn next(&mut self) {
        if self.curi == self.tokens.len() {
            return;
        }
        self.curi += 1;
    }
    fn next_noeof(&mut self, expected: &str) -> Result<(), String> {
        self.next();
        if self.curi == self.tokens.len() {
            err!("Expected {expected} but reached end of usage pattern.")
        }
        Ok(())
    }
    fn cur(&self) -> &str {
        &self.tokens[self.curi]
    }
    fn atis(&self, offset: usize, is: &str) -> bool {
        let i = self.curi + offset;
        i < self.tokens.len() && self.tokens[i] == is
    }
}

#[derive(Clone, Debug)]
enum Pattern {
    Alternates(Vec<Pattern>),
    Sequence(Vec<Pattern>),
    Optional(Vec<Pattern>),
    Repeat(Box<Pattern>),
    PatAtom(Atom),
}

#[allow(clippy::derive_ord_xor_partial_ord)]
#[derive(PartialEq, Eq, Ord, Hash, Clone, Debug)]
pub enum Atom {
    Short(char),
    Long(String),
    Command(String),
    Positional(String),
}

#[derive(Clone, Debug)]
pub struct Options {
    /// Set to true if this atom is ever repeated in any context.
    /// For positional arguments, non-argument flags and commands, repetition
    /// means that they become countable.
    /// For flags with arguments, repetition means multiple distinct values
    /// can be specified (and are represented as a Vec).
    pub repeats: bool,

    /// This specifies whether this atom has any arguments.
    /// For commands and positional arguments, this is always Zero.
    /// Flags can have zero or one argument, with an optionally default value.
    pub arg: Argument,

    /// Whether it shows up in the "options description" second.
    pub is_desc: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Argument {
    Zero,
    One(Option<String>), // optional default value
}

impl Pattern {
    fn add_options_shortcut(&mut self, par: &Parser) {
        fn add(pat: &mut Pattern, all_atoms: &AHashSet<Atom>, par: &Parser) {
            match *pat {
                Alternates(ref mut ps) | Sequence(ref mut ps) => {
                    for p in ps.iter_mut() {
                        add(p, all_atoms, par);
                    }
                }
                Repeat(ref mut p) => add(p, all_atoms, par),
                PatAtom(_) => {}
                Optional(ref mut ps) => {
                    if ps.is_empty() {
                        for atom in par.options_atoms() {
                            if !all_atoms.contains(&atom) {
                                if par.has_repeat(&atom) {
                                    ps.push(Pattern::repeat(PatAtom(atom)));
                                } else {
                                    ps.push(PatAtom(atom));
                                }
                            }
                        }
                    } else {
                        for p in &mut *ps {
                            add(p, all_atoms, par);
                        }
                    }
                }
            }
        }
        let all_atoms = self.all_atoms();
        add(self, &all_atoms, par);
    }

    fn all_atoms(&self) -> AHashSet<Atom> {
        fn all_atoms(pat: &Pattern, set: &mut AHashSet<Atom>) {
            match *pat {
                Alternates(ref ps) | Sequence(ref ps) | Optional(ref ps) => {
                    for p in ps {
                        all_atoms(p, set);
                    }
                }
                Repeat(ref p) => all_atoms(p, set),
                PatAtom(ref a) => {
                    set.insert(a.clone());
                }
            }
        }
        let mut set = AHashSet::new();
        all_atoms(self, &mut set);
        set
    }

    fn tag_repeats(&self, map: &mut SynonymMap<Atom, Options>) {
        fn dotag(
            p: &Pattern,
            rep: bool,
            map: &mut SynonymMap<Atom, Options>,
            seen: &mut AHashSet<Atom>,
        ) {
            match *p {
                Alternates(ref ps) => {
                    // This is a bit tricky. Basically, we don't want the
                    // existence of an item in mutually exclusive alternations
                    // to affect whether it repeats or not.
                    // However, we still need to record seeing each item in
                    // each alternation.
                    let fresh = seen.clone();
                    for p in ps {
                        let mut isolated = fresh.clone();
                        dotag(p, rep, map, &mut isolated);
                        for a in isolated {
                            seen.insert(a);
                        }
                    }
                }
                Sequence(ref ps) | Optional(ref ps) => {
                    for p in ps {
                        dotag(p, rep, map, seen);
                    }
                }
                Repeat(ref p) => dotag(p, true, map, seen),
                PatAtom(ref atom) => {
                    let opt = map.find_mut(atom).expect("bug: no atom found");
                    opt.repeats = opt.repeats || rep || seen.contains(atom);
                    seen.insert(atom.clone());
                }
            }
        }
        let mut seen = AHashSet::new();
        dotag(self, false, map, &mut seen);
    }

    fn repeat(p: Pattern) -> Pattern {
        match p {
            p @ Repeat(_) => p,
            p => Repeat(Box::new(p)),
        }
    }
}

impl Atom {
    pub fn new(s: &str) -> Atom {
        if Atom::is_short(s) {
            Short(s[1..].chars().next().unwrap())
        } else if Atom::is_long(s) {
            Long(s[2..].into())
        } else if Atom::is_arg(s) {
            if s.starts_with('<') && s.ends_with('>') {
                Positional(s[1..s.len() - 1].into())
            } else {
                Positional(s.into())
            }
        } else if Atom::is_cmd(s) {
            Command(s.into())
        } else {
            panic!("Unknown atom string: '{s}'")
        }
    }

    fn is_short(s: &str) -> bool {
        decl_regex! {
            IS_SHORT_RE: r"^-[^-]\S*$";
        }
        IS_SHORT_RE.is_match(s)
    }

    fn is_long(s: &str) -> bool {
        decl_regex! {
            IS_LONG_RE: r"^--\S+(?:<[^>]+>)?$";
        }
        IS_LONG_RE.is_match(s)
    }

    fn is_long_argv(s: &str) -> bool {
        decl_regex! {
            IS_LONG_ARGV_RE: r"^--\S+(=.+)?$";
        }
        IS_LONG_ARGV_RE.is_match(s)
    }

    fn is_arg(s: &str) -> bool {
        decl_regex! {
            IS_ARG_RE: r"^(\p{Lu}+|<[^>]+>)$";
        }
        IS_ARG_RE.is_match(s)
    }

    fn is_cmd(s: &str) -> bool {
        decl_regex! {
            IS_CMD_RE: r"^(-|--|[^-]\S*)$";
        }
        IS_CMD_RE.is_match(s)
    }

    // NOTE: NO LONGER NEEDED WHEN WE SIMPLIFIED partial_cmp
    // Assigns an integer to each variant of Atom. (For easier sorting.)
    // const fn type_as_usize(&self) -> usize {
    //     match *self {
    //         Short(_) => 0,
    //         Long(_) => 1,
    //         Command(_) => 2,
    //         Positional(_) => 3,
    //     }
    // }
}

impl PartialOrd for Atom {
    fn partial_cmp(&self, other: &Atom) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Short(c) => write!(f, "-{c}"),
            Long(ref s) => write!(f, "--{s}"),
            Command(ref s) => write!(f, "{s}"),
            Positional(ref s) => {
                if s.chars().all(char::is_uppercase) {
                    write!(f, "{s}")
                } else {
                    write!(f, "<{s}>")
                }
            }
        }
    }
}

impl Options {
    const fn new(rep: bool, arg: Argument) -> Options {
        Options {
            repeats: rep,
            arg,
            is_desc: false,
        }
    }
}

impl Argument {
    const fn has_arg(&self) -> bool {
        match *self {
            Zero => false,
            One(_) => true,
        }
    }
}

#[doc(hidden)]
pub struct Argv<'a> {
    /// A representation of an argv string as an ordered list of tokens.
    /// This contains only positional arguments and commands.
    positional: Vec<ArgvToken>,
    /// Same as positional, but contains short and long flags.
    /// Each flag may have an argument string.
    flags:      Vec<ArgvToken>,
    /// Counts the number of times each flag appears.
    counts:     AHashMap<Atom, usize>,

    // State for parser.
    dopt:          &'a Parser,
    argv:          Vec<String>,
    curi:          usize,
    options_first: bool,
}

#[derive(Clone, Debug)]
struct ArgvToken {
    atom: Atom,
    arg:  Option<String>,
}

impl<'a> Argv<'a> {
    fn new(dopt: &'a Parser, argv: &[String], options_first: bool) -> Result<Argv<'a>, String> {
        let mut a = Argv {
            positional: vec![],
            flags: vec![],
            counts: AHashMap::new(),
            dopt,
            argv: argv.to_vec(),
            curi: 0,
            options_first,
        };
        a.parse()?;
        for flag in &a.flags {
            match a.counts.entry(flag.atom.clone()) {
                Vacant(v) => {
                    v.insert(1);
                }
                Occupied(mut v) => {
                    *v.get_mut() += 1;
                }
            }
        }
        Ok(a)
    }

    fn parse(&mut self) -> Result<(), String> {
        let mut seen_double_dash = false;
        while self.curi < self.argv.len() {
            let current_arg = self.cur();
            let do_flags = !seen_double_dash && (!self.options_first || self.positional.is_empty());

            if do_flags && Atom::is_short(current_arg) {
                let stacked: String = current_arg[1..].into();
                for (i, c) in stacked.chars().enumerate() {
                    let mut tok = ArgvToken {
                        atom: self.dopt.descs.resolve(&Short(c)),
                        arg:  None,
                    };
                    if !self.dopt.descs.contains_key(&tok.atom) {
                        err!("Unknown flag: '{}'", &tok.atom);
                    }
                    if self.dopt.has_arg(&tok.atom) {
                        let rest = &stacked[i + 1..];
                        tok.arg = Some(if rest.is_empty() {
                            let arg = self.next_arg(&tok.atom)?;
                            arg.into()
                        } else {
                            rest.into()
                        });
                        self.flags.push(tok);
                        // We've either produced an error or gobbled up the
                        // rest of these stacked short flags, so stop.
                        break;
                    }
                    self.flags.push(tok);
                }
            } else if do_flags && Atom::is_long_argv(current_arg) {
                let (atom, mut arg) = parse_long_equal_argv(current_arg);
                let atom = self.dopt.descs.resolve(&atom);
                if !self.dopt.descs.contains_key(&atom) {
                    return self.err_unknown_flag(&atom);
                }
                if arg.is_some() && !self.dopt.has_arg(&atom) {
                    err!(
                        "Flag '{}' cannot have an argument, but found '{}'.",
                        &atom,
                        arg.as_ref().unwrap()
                    )
                } else if arg.is_none() && self.dopt.has_arg(&atom) {
                    self.next_noeof(&format!("argument for flag '{}'", &atom))?;
                    arg = Some(self.cur().into());
                }
                self.flags.push(ArgvToken { atom, arg });
            } else if !seen_double_dash && current_arg == "--" {
                seen_double_dash = true;
            } else {
                // Yup, we *always* insert a positional argument, which
                // means we completely neglect `Command` here.
                // This is because we can't tell whether something is a
                // `command` or not until we start pattern matching.
                let tok = ArgvToken {
                    atom: Positional(current_arg.into()),
                    arg:  None,
                };
                self.positional.push(tok);
            }
            self.next();
        }
        Ok(())
    }

    fn err_unknown_flag(&self, atom: &Atom) -> Result<(), String> {
        use std::usize::MAX;
        let mut best = String::new();
        let flag = atom.to_string();
        let mut min = MAX;

        let mut possibles = Vec::new();

        for (key, _) in self.dopt.descs.synonyms() {
            possibles.push(key);
        }

        for key in self.dopt.descs.keys() {
            possibles.push(key);
        }

        for key in &possibles {
            match **key {
                Long(_) | Command(_) => {
                    let name = key.to_string();
                    let dist = levenshtein(&flag, &name);
                    if dist < 3 && dist < min {
                        min = dist;
                        best = name;
                    }
                }
                _ => {}
            }
        }
        if best.is_empty() {
            err!("Unknown flag: '{}'", &atom);
        }
        err!("Unknown flag: '{}'. Did you mean '{}'?", &atom, &best)
    }

    fn cur(&self) -> &str {
        self.at(0)
    }
    fn at(&self, i: usize) -> &str {
        &self.argv[self.curi + i]
    }
    fn next(&mut self) {
        if self.curi < self.argv.len() {
            self.curi += 1;
        }
    }
    #[inline]
    fn next_arg(&mut self, atom: &Atom) -> Result<&str, String> {
        let expected = format!("argument for flag '{atom}'");
        self.next_noeof(&expected)?;
        Ok(self.cur())
    }
    fn next_noeof(&mut self, expected: &str) -> Result<(), String> {
        self.next();
        if self.curi == self.argv.len() {
            err!("Expected {expected} but reached end of arguments.")
        }
        Ok(())
    }
}

impl<'a> fmt::Debug for Argv<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        writeln!(f, "Positional: {:?}", self.positional)?;
        writeln!(f, "Flags: {:?}", self.flags)?;
        writeln!(f, "Counts: {:?}", self.counts)?;
        Ok(())
    }
}

struct Matcher<'a, 'b: 'a> {
    argv: &'a Argv<'b>,
}

#[derive(Clone, Debug, PartialEq)]
struct MState {
    argvi:      usize,                 // index into Argv.positional
    counts:     AHashMap<Atom, usize>, // flags remaining for pattern consumption
    max_counts: AHashMap<Atom, usize>, // optional flag appearances
    vals:       AHashMap<Atom, Value>,
}

impl MState {
    fn fill_value(&mut self, key: Atom, rep: bool, arg: Option<String>) -> bool {
        match (arg, rep) {
            (None, false) => {
                self.vals.insert(key, Switch(true));
            }
            (Some(arg), false) => {
                self.vals.insert(key, Plain(Some(arg)));
            }
            (None, true) => match self.vals.entry(key) {
                Vacant(v) => {
                    v.insert(Counted(1));
                }
                Occupied(mut v) => match *v.get_mut() {
                    Counted(ref mut c) => {
                        *c += 1;
                    }
                    _ => return false,
                },
            },
            (Some(arg), true) => match self.vals.entry(key) {
                Vacant(v) => {
                    v.insert(List(vec![arg]));
                }
                Occupied(mut v) => match *v.get_mut() {
                    List(ref mut vs) => vs.push(arg),
                    _ => return false,
                },
            },
        }
        true
    }

    #[inline]
    fn add_value(
        &mut self,
        opts: &Options,
        spec: &Atom,
        atom: &Atom,
        arg: &Option<String>,
    ) -> bool {
        assert!(
            opts.arg.has_arg() == arg.is_some(),
            "'{atom:?}' should have an argument but doesn't"
        );
        match *atom {
            Short(_) | Long(_) => self.fill_value(spec.clone(), opts.repeats, arg.clone()),
            Positional(ref v) => {
                assert!(!opts.arg.has_arg());
                self.fill_value(spec.clone(), opts.repeats, Some(v.clone()))
            }
            Command(_) => {
                assert!(!opts.arg.has_arg());
                self.fill_value(spec.clone(), opts.repeats, None)
            }
        }
    }

    #[inline]
    fn use_flag(&mut self, flag: &Atom) -> bool {
        match self.max_counts.entry(flag.clone()) {
            Vacant(v) => {
                v.insert(0);
            }
            Occupied(_) => {}
        }
        match self.counts.entry(flag.clone()) {
            Vacant(_) => false,
            Occupied(mut v) => {
                let c = v.get_mut();
                if *c == 0 {
                    false
                } else {
                    *c -= 1;
                    true
                }
            }
        }
    }

    #[inline]
    fn use_optional_flag(&mut self, flag: &Atom) {
        match self.max_counts.entry(flag.clone()) {
            Vacant(v) => {
                v.insert(1);
            }
            Occupied(mut v) => {
                *v.get_mut() += 1;
            }
        }
    }

    #[inline]
    fn match_cmd_or_posarg(&mut self, spec: &Atom, argv: &ArgvToken) -> Option<ArgvToken> {
        match (spec, &argv.atom) {
            (_, &Command(_)) => {
                // This is impossible because the argv parser doesn't know
                // how to produce `Command` values.
                unreachable!()
            }
            (Command(n1), Positional(n2)) if n1 == n2 => {
                // Coerce a positional to a command because the pattern
                // demands it and the positional argument matches it.
                self.argvi += 1;
                Some(ArgvToken {
                    atom: spec.clone(),
                    arg:  None,
                })
            }
            (&Positional(_), _) => {
                self.argvi += 1;
                Some(argv.clone())
            }
            _ => None,
        }
    }
}

impl<'a, 'b> Matcher<'a, 'b> {
    fn matches(argv: &'a Argv<'_>, pat: &Pattern) -> Option<SynonymMap<String, Value>> {
        let m = Matcher { argv };
        let init = MState {
            argvi:      0,
            counts:     argv.counts.clone(),
            max_counts: AHashMap::new(),
            vals:       AHashMap::new(),
        };
        m.states(pat, &init)
            .into_iter()
            .filter(|s| m.state_consumed_all_argv(s))
            .filter(|s| m.state_has_valid_flags(s))
            .find(|s| m.state_valid_num_flags(s))
            .map(|mut s| {
                m.add_flag_values(&mut s);
                m.add_default_values(&mut s);

                // Build a synonym map so that it's easier to look up values.
                let mut synmap: SynonymMap<String, Value> = SynonymMap::new();
                for (k, v) in s.vals {
                    synmap.insert(k.to_string(), v);
                }
                for (from, to) in argv.dopt.descs.synonyms() {
                    let (from, to) = (from.to_string(), to.to_string());
                    if synmap.contains_key(&to) {
                        synmap.insert_synonym(from, to);
                    }
                }
                synmap
            })
    }

    fn token_from(&self, state: &MState) -> Option<&ArgvToken> {
        self.argv.positional.get(state.argvi)
    }

    #[inline]
    fn add_value(
        &self,
        state: &mut MState,
        atom_spec: &Atom,
        atom: &Atom,
        arg: &Option<String>,
    ) -> bool {
        let opts = self.argv.dopt.descs.get(atom_spec);
        state.add_value(opts, atom_spec, atom, arg)
    }

    #[inline]
    fn add_flag_values(&self, state: &mut MState) {
        for tok in &self.argv.flags {
            self.add_value(state, &tok.atom, &tok.atom, &tok.arg);
        }
    }

    #[inline]
    fn add_default_values(&self, state: &mut MState) {
        decl_regex! {
            SPLIT_SPACE: r"\s+";
        }
        let vs = &mut state.vals;
        for (a, opts) in self.argv.dopt.descs.iter() {
            if vs.contains_key(a) {
                continue;
            }
            let atom = a.clone();
            match (opts.repeats, &opts.arg) {
                (false, &Zero) => {
                    match *a {
                        Positional(_) => vs.insert(atom, Plain(None)),
                        _ => vs.insert(atom, Switch(false)),
                    };
                }
                (true, &Zero) => {
                    match *a {
                        Positional(_) => vs.insert(atom, List(vec![])),
                        _ => vs.insert(atom, Counted(0)),
                    };
                }
                (false, &One(None)) => {
                    vs.insert(atom, Plain(None));
                }
                (true, &One(None)) => {
                    vs.insert(atom, List(vec![]));
                }
                (false, &One(Some(ref v))) => {
                    vs.insert(atom, Plain(Some(v.clone())));
                }
                (true, &One(Some(ref v))) => {
                    let words = SPLIT_SPACE
                        .split(v)
                        .map(std::borrow::ToOwned::to_owned)
                        .collect();
                    vs.insert(atom, List(words));
                }
            }
        }
    }

    #[inline]
    fn state_consumed_all_argv(&self, state: &MState) -> bool {
        self.argv.positional.len() == state.argvi
    }

    #[inline]
    fn state_has_valid_flags(&self, state: &MState) -> bool {
        self.argv
            .counts
            .keys()
            .all(|flag| state.max_counts.contains_key(flag))
    }

    #[inline]
    fn state_valid_num_flags(&self, state: &MState) -> bool {
        state
            .counts
            .iter()
            .all(|(flag, count)| count <= &state.max_counts[flag])
    }

    #[inline]
    fn states(&self, pat: &Pattern, init: &MState) -> Vec<MState> {
        match *pat {
            Alternates(ref ps) => {
                let mut alt_states = vec![];
                for p in ps {
                    alt_states.extend(self.states(p, init));
                }
                alt_states
            }
            Sequence(ref ps) => {
                let (mut states, mut next) = (vec![], vec![]);
                let mut iter = ps.iter();
                match iter.next() {
                    None => return vec![init.clone()],
                    Some(p) => states.extend(self.states(p, init)),
                }
                for p in iter {
                    for s in states {
                        next.extend(self.states(p, &s));
                    }
                    states = vec![];
                    states.extend(next);
                    next = vec![];
                }
                states
            }
            Optional(ref ps) => {
                let mut base = init.clone();
                let mut noflags = vec![];
                for p in ps {
                    match p {
                        // Prevent exponential growth in cases like [--flag...]
                        // See https://github.com/docopt/docopt.rs/issues/195
                        Repeat(b) => match &**b {
                            &PatAtom(ref a @ Short(_)) | &PatAtom(ref a @ Long(_)) => {
                                let argv_count = self.argv.counts.get(a).map_or(0, |&x| x);
                                let max_count = base.max_counts.get(a).map_or(0, |&x| x);
                                if argv_count > max_count {
                                    for _ in max_count..argv_count {
                                        base.use_optional_flag(a);
                                    }
                                }
                            }
                            _ => {
                                noflags.push(p);
                            }
                        },
                        &PatAtom(ref a @ Short(_)) | &PatAtom(ref a @ Long(_)) => {
                            let argv_count = self.argv.counts.get(a).map_or(0, |&x| x);
                            let max_count = base.max_counts.get(a).map_or(0, |&x| x);
                            if argv_count > max_count {
                                base.use_optional_flag(a);
                            }
                        }
                        other => {
                            noflags.push(other);
                        }
                    }
                }
                let mut states = vec![];
                self.all_option_states(&base, &mut states, &noflags);
                states
            }
            Repeat(ref p) => match &**p {
                &PatAtom(ref a @ Short(_)) | &PatAtom(ref a @ Long(_)) => {
                    let mut bases = self.states(p, init);
                    for base in &mut bases {
                        let argv_count = self.argv.counts.get(a).map_or(0, |&x| x);
                        let max_count = base.max_counts.get(a).map_or(0, |&x| x);
                        if argv_count > max_count {
                            for _ in max_count..argv_count {
                                base.use_optional_flag(a);
                            }
                        }
                    }
                    bases
                }
                _ => {
                    let mut grouped_states = vec![self.states(p, init)];
                    loop {
                        let mut nextss = vec![];
                        for s in grouped_states.last().unwrap() {
                            nextss.extend(self.states(p, s).into_iter().filter(|snext| snext != s));
                        }
                        if nextss.is_empty() {
                            break;
                        }
                        grouped_states.push(nextss);
                    }
                    grouped_states
                        .into_iter()
                        .flat_map(std::iter::IntoIterator::into_iter)
                        .collect::<Vec<MState>>()
                }
            },
            PatAtom(ref atom) => {
                let mut state = init.clone();
                match *atom {
                    Short(_) | Long(_) => {
                        if !state.use_flag(atom) {
                            return vec![];
                        }
                    }
                    Command(_) | Positional(_) => {
                        let tok = match self.token_from(init) {
                            None => return vec![],
                            Some(tok) => tok,
                        };
                        let tok = match state.match_cmd_or_posarg(atom, tok) {
                            None => return vec![],
                            Some(tok) => tok,
                        };
                        if !self.add_value(&mut state, atom, &tok.atom, &tok.arg) {
                            return vec![];
                        }
                    }
                }
                vec![state]
            }
        }
    }

    #[inline]
    fn all_option_states(&self, base: &MState, states: &mut Vec<MState>, pats: &[&Pattern]) {
        if pats.is_empty() {
            states.push(base.clone());
        } else {
            let (pat, rest) = (*pats.first().unwrap(), &pats[1..]);
            for s in self.states(pat, base) {
                self.all_option_states(&s, states, rest);
            }
            // Order is important here! This must come after the loop above
            // because we prefer presence over absence. The first state wins.
            self.all_option_states(base, states, &pats[1..]);
        }
    }
}

// Tries to parse a long flag of the form '--flag[=arg]' and returns a tuple
// with the flag atom and whether there is an argument or not.
// If '=arg' exists and 'arg' isn't a valid argument, an error is returned.
fn parse_long_equal(flag: &str) -> Result<(Atom, Argument), String> {
    decl_regex! {
        LONG_EQUAL: "^(?P<name>[^=]+)=(?P<arg>.+)$";
    }
    if let Some(cap) = LONG_EQUAL.captures(flag) {
        let arg = cap_or_empty(&cap, "arg");
        if !Atom::is_arg(arg) {
            err!("Argument '{flag}' for flag '{arg}' is not in the form ARG or <arg>.")
        }
        Ok((Atom::new(cap_or_empty(&cap, "name")), One(None)))
    } else {
        Ok((Atom::new(flag), Zero))
    }
}

fn parse_long_equal_argv(flag: &str) -> (Atom, Option<String>) {
    decl_regex! {
        LONG_EQUAL: "^(?P<name>[^=]+)=(?P<arg>.*)$";
    }
    if let Some(cap) = LONG_EQUAL.captures(flag) {
        (
            Atom::new(cap_or_empty(&cap, "name")),
            Some(cap_or_empty(&cap, "arg").to_string()),
        )
    } else {
        (Atom::new(flag), None)
    }
}

// Tokenizes a usage pattern.
// Beware: regex hack ahead. Tokenizes based on whitespace separated words.
// It first normalizes `[xyz]` -> `[ xyz ]` so that delimiters are tokens.
// Similarly for `...`, `(`, `)` and `|`.
// One hitch: `--flag=<arg spaces>` is allowed, so we use a regex to pick out
// words.
fn pattern_tokens(pat: &str) -> Vec<String> {
    decl_regex! {
        NORMALIZE: r"\.\.\.|\[|\]|\(|\)|\|";
        WORDS: r"--\S+?=<[^>]+>|<[^>]+>|\S+";
    }

    let pat = NORMALIZE.replace_all(pat.trim(), " $0 ");
    WORDS
        .captures_iter(&pat)
        .map(|cap| cap[0].to_string())
        .collect()
}
