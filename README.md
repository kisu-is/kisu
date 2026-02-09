<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="./logo/dark.svg">
    <img
      src="./logo/light.svg"
      height="240px"
    >
  </picture>
</p>

<p align="center">
Lazy purely functional configuration language
</p>

Current syntax example:
```haskell
struct Dependency {
  name: String;
  version: String;
}

struct Package {
  name: String;
  edition: String;
  dependencies: [Dependency];
}

mk_dep = |name, version|: Dependency {
  name;
  version;
};

Package {
  name = "kisu";
  edition = "2024";

  dependencies = [
    mk_dep "logos" "*",
    mk_dep "serde" "*",
    mk_dep "miette" "*",
  ];
}
```

