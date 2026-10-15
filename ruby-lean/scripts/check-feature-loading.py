#!/usr/bin/env python3
"""Compare require scope/cache/retry with CRuby using identical feature source.

Run after `lake build rubycore`. A test-only Lean entry point registers an exact
feature body, independently of the smaller standard-library implementations.
"""
from pathlib import Path
import json
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
HOMEBREW_RUBY = Path('/opt/homebrew/opt/ruby/bin/ruby')
RUBY = os.environ.get('DIFFTEST_RUBY') or (
    str(HOMEBREW_RUBY) if HOMEBREW_RUBY.exists() else shutil.which('ruby')
)
if not RUBY:
    raise SystemExit('CRuby is required; set DIFFTEST_RUBY')

CASES = [
    ('exception, reentry, scope and cache', '''
$loads = ($loads || 0) + 1
p [:body, $loads, require('loader-spec')]
LoaderMarker = 7
raise 'first load fails' if $loads == 1
''', '''
module LoaderCaller
  def self.run
    begin
      require 'loader-spec'
    rescue => e
      p e.message
    end
    p [LoaderMarker, $loads, const_defined?(:LoaderMarker, false)]
    p require('loader-spec.rb')
    p require('loader-spec')
    p $loads
  end
end
LoaderCaller.run
'''),
    ('throw and ensure', '''
$loads = ($loads || 0) + 1
begin
  throw :stop_loading, :partial if $loads == 1
ensure
  p [:ensure, $loads]
end
''', '''
p catch(:stop_loading) { require 'loader-spec' }
p require('loader-spec')
p require('loader-spec.rb')
p $loads
'''),
    ('completed dependency survives failure', '''
$loads = ($loads || 0) + 1
p [:json, require('json')]
raise 'first load fails' if $loads == 1
''', '''
2.times do
  begin
    p require('loader-spec')
  rescue => e
    p e.message
  end
end
p [require('json'), require('loader-spec')]
p JSON.generate([1, true, nil])
'''),
]


def export(source):
    result = subprocess.run(
        [RUBY, str(ROOT / 'desugar/bin/export-json')], input=source,
        text=True, capture_output=True, check=True,
    )
    return json.loads(result.stdout)


for name, feature, program in CASES:
    with tempfile.TemporaryDirectory(prefix='loader-spec-') as directory:
        Path(directory, 'loader-spec.rb').write_text(feature)
        control = subprocess.run(
            [RUBY, '-I', directory], input=program,
            text=True, capture_output=True, check=True,
        )
        model = subprocess.run(
            ['lake', 'env', 'lean', '--run',
             str(ROOT / 'ruby-lean/scripts/feature_loading_runner.lean')],
            cwd=ROOT / 'ruby-lean',
            input=json.dumps({'feature': export(feature), 'program': export(program)}),
            text=True, capture_output=True, check=True,
        )
        observation = json.loads(model.stdout)
        assert observation['exception'] is None, (name, observation)
        assert observation['stdout'] == control.stdout, (name, control.stdout, observation)
        print(f'AGREE: {name}')


# ── require_relative over the VFS (issue #7 / M1) ────────────────────────────
# The libraries live in the model's boot fixture (ruby-lean/prelude/vfs/lib/);
# CRuby gets the identical files in a temp dir. `require_relative` is relative,
# so the two agree regardless of the differing absolute prefix as long as the
# programs don't print an absolute path. The model program's own path is
# /lib/main.rb, a sibling of the fixture libraries.
VFS_LIB = ROOT / 'ruby-lean/prelude/vfs/lib'

RELATIVE_CASES = [
    ('require_relative: load, transitive, cache, dedup', '''
p require_relative("greeting")
p require_relative("greeting")
p GREETING
p greet(3)
p HELPER_CONST
p require_relative("helper")
'''),
    ('require_relative: circular load returns false mid-load', '''
p require_relative("cyc_a")
p $cyc
'''),
    ('require_relative: explicit .rb and leading path', '''
p require_relative("greeting.rb")
p require_relative("./helper")
'''),
]

for name, program in RELATIVE_CASES:
    with tempfile.TemporaryDirectory(prefix='vfs-lib-') as directory:
        lib = Path(directory, 'lib')
        lib.mkdir()
        for source in VFS_LIB.glob('*.rb'):
            (lib / source.name).write_text(source.read_text())
        (lib / 'main.rb').write_text(program)
        control = subprocess.run(
            [RUBY, str(lib / 'main.rb')],
            text=True, capture_output=True, check=True,
        )
        model = subprocess.run(
            ['lake', 'env', 'lean', '--run',
             str(ROOT / 'ruby-lean/scripts/require_relative_runner.lean')],
            cwd=ROOT / 'ruby-lean',
            input=json.dumps({'program': export(program), 'path': '/lib/main.rb'}),
            text=True, capture_output=True, check=True,
        )
        observation = json.loads(model.stdout)
        assert observation['exception'] is None, (name, observation)
        assert observation['stdout'] == control.stdout, (name, control.stdout, observation)
        print(f'AGREE: {name}')
