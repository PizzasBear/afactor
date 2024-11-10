use std::fmt;

/// Optional [`u32`] with the value [`u32::MAX`] reserved for [`None`]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct OptU32(u32);

impl fmt::Debug for OptU32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.get(), f)
    }
}

impl Default for OptU32 {
    fn default() -> Self {
        Self::none()
    }
}

impl OptU32 {
    pub const NONE: Self = Self::none();

    #[must_use]
    #[inline]
    pub fn new(value: Option<u32>) -> Self {
        match value {
            Some(value) => Self::some(value),
            None => Self::none(),
        }
    }
    #[must_use]
    #[inline]
    pub const fn new_checked(value: Option<u32>) -> Option<Self> {
        match value {
            Some(value) => Self::some_checked(value),
            None => Some(Self::none()),
        }
    }
    #[must_use]
    #[inline]
    pub const fn new_unchecked(value: Option<u32>) -> Self {
        match value {
            Some(value) => Self::some_unchecked(value),
            None => Self::none(),
        }
    }
    #[must_use]
    #[inline]
    pub const fn none() -> Self {
        Self(u32::MAX)
    }
    #[must_use]
    #[inline]
    pub fn some(value: u32) -> Self {
        Self::some_checked(value).expect("`OptU32` value cannot be `u32::MAX` as it is reserved")
    }
    #[must_use]
    #[inline]
    pub const fn some_checked(value: u32) -> Option<Self> {
        let slf = Self::some_unchecked(value);
        match slf.get() {
            Some(_) => Some(slf),
            None => None,
        }
    }
    #[must_use]
    #[inline]
    pub const fn some_unchecked(value: u32) -> Self {
        Self(value)
    }
    #[must_use]
    #[inline]
    pub const fn get(self) -> Option<u32> {
        match self {
            Self::NONE => None,
            Self(value) => Some(value),
        }
    }
    #[must_use]
    #[inline]
    pub const fn is_none(self) -> bool {
        matches!(self, Self::NONE)
    }
    #[must_use]
    #[inline]
    pub const fn is_some(self) -> bool {
        !self.is_none()
    }
    #[must_use]
    #[inline]
    pub fn is_some_and(self, f: impl FnOnce(u32) -> bool) -> bool {
        self.get().is_some_and(f)
    }
    #[must_use]
    #[inline]
    pub fn is_none_or(self, f: impl FnOnce(u32) -> bool) -> bool {
        self.get().is_none_or(f)
    }
    #[inline]
    pub fn inspect(self, f: impl FnOnce(u32)) -> Self {
        if let Some(value) = self.get() {
            f(value);
        }
        self
    }
    #[must_use]
    #[inline]
    pub fn filter(self, predicate: impl FnOnce(u32) -> bool) -> Self {
        match self.is_none_or(predicate) {
            true => self,
            false => Self::none(),
        }
    }
    #[must_use]
    #[inline]
    pub const fn or(self, optb: Self) -> Self {
        match self.is_some() {
            true => self,
            false => optb,
        }
    }
    #[inline]
    pub fn or_else(self, f: impl FnOnce() -> Self) -> Self {
        match self.is_some() {
            true => self,
            false => f(),
        }
    }
    #[inline]
    pub fn unwrap(self) -> u32 {
        self.get().unwrap()
    }
    #[inline]
    pub fn expect(self, msg: &str) -> u32 {
        self.get().expect(msg)
    }
    #[must_use]
    #[inline]
    pub const fn unwrap_or(self, default: u32) -> u32 {
        match self.get() {
            Some(value) => value,
            None => default,
        }
    }
    #[must_use = "if you don't need the returned value, use `if let` instead"]
    #[inline]
    pub fn map_or<T>(self, default: T, f: impl FnOnce(u32) -> T) -> T {
        match self.get() {
            Some(value) => f(value),
            None => default,
        }
    }
    #[inline]
    pub fn map_or_else<T>(self, default: impl FnOnce() -> T, f: impl FnOnce(u32) -> T) -> T {
        match self.get() {
            Some(value) => f(value),
            None => default(),
        }
    }
}
