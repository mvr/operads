import Distribution.Simple
import Distribution.PackageDescription(PackageDescription)
import Distribution.Simple.LocalBuildInfo(LocalBuildInfo)
import System.Cmd(system)
import Distribution.Simple.LocalBuildInfo

main = defaultMainWithHooks (simpleUserHooks {runTests = runzeTests})

runzeTests:: Args -> Bool -> PackageDescription -> LocalBuildInfo -> IO ()
runzeTests a b pd lb = system ( "./dist/build/OperadTest/OperadTest") >> return()
