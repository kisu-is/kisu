
<p align="center">
Mauve
</p>

<p align="center">
Experimental programming language
</p>

Current syntax example:

```haskell
struct Dependency {
  name: String,
  version: String,
}

struct Package {
  name: String,
  edition: String,
  dependencies: [Dependency],
}

let mk_dep = |name, version|: Dependency {
  name,
  version,
};

Package {
  name = "mauve",
  edition = "2024",

  dependencies = [
    mk_dep "logos" "*",
    mk_dep "serde" "*",
    mk_dep "miette" "*",
  ];
}
```

