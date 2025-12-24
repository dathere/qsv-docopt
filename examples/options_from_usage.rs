use qsv_docopt::{Docopt, parse::Atom};
use std::io::Read;

// Write the Docopt usage string.
const USAGE: &str = r#"
Rust's package manager

Usage:
    cargo <command> [<args>...]
    cargo [options]

Options:
    -h, --help       Display this message
    -V, --version    Print version info and exit
    --list           List installed commands
    -v, --verbose    Use verbose output

Some common cargo commands are:
    build       Compile the current project
    clean       Remove the target directory
    doc         Build this project's and its dependencies' documentation
    new         Create a new cargo project
    run         Build and execute src/main.rs
    test        Run the tests
    bench       Run the benchmarks
    update      Update dependencies listed in Cargo.lock

See 'cargo help <command>' for more information on a specific command.
"#;

fn main() {
    let args = std::env::args().collect::<Vec<String>>();
    let mut passed_usage = USAGE.to_string();
    if let Some(arg) = args.get(1) {
        if arg == "-" {
            std::io::stdin().read_to_string(&mut passed_usage).unwrap();
            println!("{}", get_options(passed_usage.clone()).join(", "));
            return;
        } else if arg == "qsv" {
            let qsv_list = String::from_utf8(
                std::process::Command::new("qsv")
                    .arg("--list")
                    .output()
                    .unwrap()
                    .stdout,
            )
            .unwrap();
            let mut commands = vec![];
            for line in qsv_list.lines() {
                if line.starts_with("    ") {
                    let command = line.trim_start().split_whitespace().next().unwrap();
                    commands.push(command);
                }
            }
            for command in commands.iter() {
                let command_usage_text = String::from_utf8(
                    std::process::Command::new("qsv")
                        .arg(command)
                        .arg("--help")
                        .output()
                        .unwrap()
                        .stdout,
                )
                .unwrap();
                println!("{command} options:");
                let options = get_options(command_usage_text);
                println!("{}", options.join(", "));
                println!("=====================");
            }
        }
    }
    println!("{}", get_options(passed_usage).join(", "));
}

fn get_options(usage: String) -> Vec<String> {
    let docopt = Docopt::new(usage).unwrap();
    let parser = docopt.parser();
    let descs = parser.descs.clone();
    let descs: Vec<String> = descs
        .keys()
        .filter(|l| match l {
            Atom::Short(_) => true,
            Atom::Long(l) => {
                if l.starts_with("---") {
                    false
                } else {
                    true
                }
            }
            _ => false,
        })
        .map(|k| k.to_string())
        .collect();
    descs
}
