{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "hahnExt";

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  # coqproject = "_CoqProject";

  default-bundle = "8.19";

  bundles."8.16" = {
    coqPackages.coq.override.version = "8.16";
    coqPackages.hahn.override.version = "master";
  };
  bundles."8.17" = {
    coqPackages.coq.override.version = "8.17";
    coqPackages.hahn.override.version = "master";
  };
  bundles."8.18" = {
    coqPackages.coq.override.version = "8.18";
    coqPackages.hahn.override.version = "master";
  };
  bundles."8.19" = {
    coqPackages.coq.override.version = "8.19";
    coqPackages.hahn.override.version = "master";
  };

  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  
  cachix.weakmemory.authToken = "CACHIX_AUTH_TOKEN";
}
