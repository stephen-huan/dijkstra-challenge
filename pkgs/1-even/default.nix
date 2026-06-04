{ stdenv
, leanPackages
, landrun
, nanoda
}:

stdenv.mkDerivation {
  name = "1-even";
  src = ../../1-even;

  strictDeps = true;
  __structuredAttrs = true;
  preferLocalBuild = true;

  doCheck = true;

  nativeCheckInputs = [
    landrun
    leanPackages.comparator
    leanPackages.lean4
    nanoda
  ];

  checkPhase = ''
    runHook preCheck

    lake env comparator config.json

    runHook postCheck
  '';

  installPhase = ''
    runHook preInstall

    touch $out

    runHook postInstall
  '';
}
