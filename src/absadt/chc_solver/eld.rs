use super::Instance as InstanceT;
use crate::common::*;
use std::borrow::Cow;
use std::io::{BufRead, BufReader};
use std::process::{Command, Stdio};

pub struct Eldarica {
    child: std::process::Child,
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
}

const OPTION: [&str; 0] = [];

impl Eldarica {
    fn new(timeout: Option<usize>) -> Res<Self> {
        let mut args = OPTION.iter().map(|s| Cow::from(*s)).collect::<Vec<_>>();
        args.push(Cow::from("-in"));
        if let Some(timeout) = timeout {
            args.push(Cow::from(format!("-t:{}", timeout)));
        }

        let mut child = Command::new("eld")
            .args(args.iter().map(|s| s.as_ref()))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;
        let stdin = child.stdin.take().expect("no stdin");
        let stdout = child.stdout.take().expect("no stdout");
        let stdout = BufReader::new(stdout);
        Ok(Self {
            child,
            stdin,
            stdout,
        })
    }
}

impl Eldarica {
    fn dump_instance<I>(&mut self, instance: &I, encode_tag: bool) -> Res<()>
    where
        I: InstanceT,
    {
        instance.dump_as_smt2_with_encode_tag(&mut self.stdin, "", encode_tag)?;
        Ok(())
    }

    fn check_sat(self) -> Res<bool> {
        let Self {
            stdin,
            stdout,
            mut child,
            ..
        } = self;
        fn inner(
            stdin: std::process::ChildStdin,
            mut stdout: BufReader<std::process::ChildStdout>,
        ) -> Res<String> {
            stdin.discard();

            let mut line = String::new();
            stdout.read_line(&mut line)?;
            Ok(line)
        }

        let res = inner(stdin, stdout);
        // kill child proess before returning
        child.kill().unwrap();
        let line = res?;

        if line.starts_with("sat") {
            Ok(true)
        } else if line.starts_with("unsat") {
            Ok(false)
        } else {
            bail!("Unexpected output: {}", line)
        }
    }
}

pub fn run_eldarica<I>(instance: &I, timeout: Option<usize>, encode_tag: bool) -> Res<bool>
where
    I: InstanceT,
{
    let mut eld = Eldarica::new(timeout)?;
    eld.dump_instance(instance, encode_tag)?;
    eld.check_sat()
}
