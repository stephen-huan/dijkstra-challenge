{ stdenv
, leanPackages
, landrun
, nanoda
}:

stdenv.mkDerivation {
  name = "2-parity";
  src = ../../2-parity;

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
