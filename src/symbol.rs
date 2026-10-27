use std::collections::HashMap;

/// The identity of a name.  A symbol's identity is never changed by a rename.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymbolId(pub u32);

impl SymbolId {
    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Symbol {
    pub id: SymbolId,
    pub display_name: String,
}

/// Persistent interning table shared by the lexer, resolver, and compiler.
#[derive(Clone, Debug, Default)]
pub struct NameTable {
    names: HashMap<String, SymbolId>,
    symbols: Vec<Symbol>,
}

impl NameTable {
    pub fn new() -> Self {
        Self::default()
    }

    /// Return the stable symbol for a source-level name.
    pub fn intern(&mut self, name: &str) -> SymbolId {
        if let Some(&id) = self.names.get(name) {
            return id;
        }
        let id = SymbolId(self.symbols.len() as u32);
        self.names.insert(name.to_owned(), id);
        self.symbols.push(Symbol {
            id,
            display_name: name.to_owned(),
        });
        id
    }

    pub fn lookup(&self, name: &str) -> Option<SymbolId> {
        self.names.get(name).copied()
    }

    pub fn symbol(&self, id: SymbolId) -> Option<&Symbol> {
        self.symbols.get(id.0 as usize)
    }

    pub fn display_name(&self, id: SymbolId) -> Option<&str> {
        self.symbol(id).map(|s| s.display_name.as_str())
    }

    /// Rename only the presentation name.  The interned source spelling and ID
    /// remain unchanged, so all references to the symbol stay valid.
    pub fn rename(&mut self, id: SymbolId, display_name: impl Into<String>) -> bool {
        if let Some(symbol) = self.symbols.get_mut(id.0 as usize) {
            symbol.display_name = display_name.into();
            true
        } else {
            false
        }
    }

    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }
}

/// Lexical name resolver. Each declaration gets a fresh ID, while references
/// search innermost scope first and therefore handle shadowing correctly.
#[derive(Clone, Debug)]
pub struct Resolver {
    scopes: Vec<HashMap<String, SymbolId>>,
}

impl Resolver {
    pub fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
        }
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub fn pop_scope(&mut self) -> Option<HashMap<String, SymbolId>> {
        (self.scopes.len() > 1).then(|| self.scopes.pop().unwrap())
    }

    pub fn declare(&mut self, names: &mut NameTable, name: &str) -> SymbolId {
        // Declarations are distinct even when they shadow an existing name.
        let id = SymbolId(names.symbols.len() as u32);
        names.symbols.push(Symbol {
            id,
            display_name: name.to_owned(),
        });
        self.scopes.last_mut().unwrap().insert(name.to_owned(), id);
        id
    }

    pub fn resolve(&self, name: &str) -> Option<SymbolId> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
    }
}

impl Default for Resolver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rename_preserves_identity() {
        let mut table = NameTable::new();
        let id = table.intern("value");
        assert_eq!(table.intern("value"), id);
        assert!(table.rename(id, "renamed"));
        assert_eq!(table.lookup("value"), Some(id));
        assert_eq!(table.display_name(id), Some("renamed"));
    }

    #[test]
    fn resolver_prefers_inner_scope() {
        let mut table = NameTable::new();
        let mut resolver = Resolver::new();
        let outer = resolver.declare(&mut table, "x");
        resolver.push_scope();
        let inner = resolver.declare(&mut table, "x");
        assert_ne!(outer, inner);
        assert_eq!(resolver.resolve("x"), Some(inner));
        resolver.pop_scope();
        assert_eq!(resolver.resolve("x"), Some(outer));
    }
}
