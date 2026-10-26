"""Credential-boundary and lifecycle tests without Docker or GitHub access."""

import fcntl
import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import manage
import vm


def identity_archive(settings=None, *, entries=None, bom=False):
    settings = settings if settings is not None else {
        "agentId": 1,
        "ephemeral": True,
        "disableUpdate": True,
        "gitHubUrl": "https://github.com/GTimG/QuasiRiemannTracker",
    }
    encoded = json.dumps(settings).encode("utf-8-sig" if bom else "utf-8")
    if entries is None:
        entries = [
            (".runner", encoded, tarfile.REGTYPE),
            (".credentials", b'{"test": "credential"}', tarfile.REGTYPE),
            (".credentials_rsaparams", b'{"test": "key"}', tarfile.REGTYPE),
        ]
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode="w") as archive:
        for name, content, kind in entries:
            item = tarfile.TarInfo(name)
            item.type = kind
            if item.isfile():
                item.size = len(content)
            elif kind in (tarfile.SYMTYPE, tarfile.LNKTYPE):
                item.linkname = "/outside-runner"
            archive.addfile(item, io.BytesIO(content) if item.isfile() else None)
    return output.getvalue()


class IdentityBoundaryTests(unittest.TestCase):
    def test_accepts_only_repository_ephemeral_identity_including_utf8_bom(self):
        for bom in (False, True):
            with self.subTest(bom=bom):
                data = identity_archive(bom=bom)
                self.assertEqual(manage.validate_identity(data), data)

    def test_rejects_reusable_and_automatically_updating_identities(self):
        base = {
            "ephemeral": True,
            "disableUpdate": True,
            "gitHubUrl": "https://github.com/GTimG/QuasiRiemannTracker",
        }
        for field in ("ephemeral", "disableUpdate"):
            for value in (False, None, "true", 1):
                with self.subTest(field=field, value=value):
                    with self.assertRaises(RuntimeError):
                        manage.validate_identity(identity_archive({**base, field: value}))
            with self.subTest(field=field, value="missing"):
                with self.assertRaises(RuntimeError):
                    manage.validate_identity(identity_archive({k: v for k, v in base.items() if k != field}))

    def test_rejects_other_repositories_and_misleading_urls(self):
        for repository in (
            "https://github.com/attacker/repository",
            "https://github.com/GTimG",
            "http://github.com/GTimG/QuasiRiemannTracker",
            "https://github.com.evil.test/GTimG/QuasiRiemannTracker",
            "https://github.com/GTimG/QuasiRiemannTracker/../other",
            "https://github.com/GTimG/QuasiRiemannTracker?repository=other",
            "",
        ):
            with self.subTest(repository=repository):
                with self.assertRaises(RuntimeError):
                    manage.validate_identity(identity_archive({
                        "ephemeral": True, "disableUpdate": True, "gitHubUrl": repository,
                    }))

    def test_rejects_extra_missing_duplicate_and_path_escape_entries(self):
        good = [
            (".runner", b"{}", tarfile.REGTYPE),
            (".credentials", b"{}", tarfile.REGTYPE),
            (".credentials_rsaparams", b"{}", tarfile.REGTYPE),
        ]
        attacks = [good[:2], good + [(".env", b"injected", tarfile.REGTYPE)]]
        for name in (".runner", "../.credentials_rsaparams", "/.credentials_rsaparams", "./.credentials_rsaparams"):
            attacks.append(good[:2] + [(name, b"{}", tarfile.REGTYPE)])
        for entries in attacks:
            with self.subTest(names=[entry[0] for entry in entries]):
                with self.assertRaises(RuntimeError):
                    manage.validate_identity(identity_archive(entries=entries))

    def test_rejects_link_device_and_directory_entries(self):
        for kind in (tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.DIRTYPE, tarfile.CHRTYPE, tarfile.BLKTYPE, tarfile.FIFOTYPE):
            with self.subTest(kind=kind):
                with self.assertRaises(RuntimeError):
                    manage.validate_identity(identity_archive(entries=[
                        (".runner", b"{}", tarfile.REGTYPE),
                        (".credentials", b"{}", tarfile.REGTYPE),
                        (".credentials_rsaparams", b"", kind),
                    ]))

    def test_rejects_empty_oversized_and_unbounded_bootstrap_data(self):
        for content in (b"", b"x" * 262145):
            with self.subTest(size=len(content)):
                with self.assertRaises(RuntimeError):
                    manage.validate_identity(identity_archive(entries=[
                        (".runner", b"{}", tarfile.REGTYPE),
                        (".credentials", b"{}", tarfile.REGTYPE),
                        (".credentials_rsaparams", content, tarfile.REGTYPE),
                    ]))
        with self.assertRaises(RuntimeError):
            manage.validate_identity(b"x" * (1024 * 1024 + 1))


class VMIdentityBoundaryTests(unittest.TestCase):
    def test_vm_keeps_credentials_and_forces_work_into_guest_workspace(self):
        settings = {"ephemeral": True, "disableUpdate": True,
                    "gitHubUrl": vm.REPOSITORY, "workFolder": "/etc"}
        for bom in (False, True):
            with self.subTest(bom=bom):
                files = vm.read_identity(io.BytesIO(identity_archive(settings, bom=bom)))
                self.assertEqual(set(files), {".runner", ".credentials", ".credentials_rsaparams"})
                self.assertEqual(json.loads(files[".runner"])["workFolder"], "_work")
                self.assertEqual(files[".credentials"], b'{"test": "credential"}')
                self.assertEqual(files[".credentials_rsaparams"], b'{"test": "key"}')

    def test_vm_independently_rejects_reusable_or_wrong_repository_identity(self):
        settings = {"ephemeral": True, "disableUpdate": True, "gitHubUrl": vm.REPOSITORY}
        for field in ("ephemeral", "disableUpdate"):
            for value in (False, None, "true", 1):
                with self.subTest(field=field, value=value):
                    with self.assertRaises(ValueError):
                        vm.read_identity(io.BytesIO(identity_archive({**settings, field: value})))
        for repository in ("https://github.com/attacker/repo", vm.REPOSITORY + "/../other",
                           vm.REPOSITORY + "?repository=other", ""):
            with self.subTest(repository=repository):
                with self.assertRaises(ValueError):
                    vm.read_identity(io.BytesIO(identity_archive({**settings, "gitHubUrl": repository})))

    def test_vm_rejects_archive_path_link_duplicate_and_extra_entries(self):
        settings = {"ephemeral": True, "disableUpdate": True, "gitHubUrl": vm.REPOSITORY}
        good = [(".runner", json.dumps(settings).encode(), tarfile.REGTYPE),
                (".credentials", b"{}", tarfile.REGTYPE),
                (".credentials_rsaparams", b"{}", tarfile.REGTYPE)]
        attacks = [good[:2], good + [(".env", b"injected", tarfile.REGTYPE)], good + [good[-1]]]
        attacks += [good[:2] + [(name, b"{}", tarfile.REGTYPE)]
                    for name in ("../.credentials_rsaparams", "/.credentials_rsaparams")]
        attacks += [good[:2] + [(".credentials_rsaparams", b"", kind)]
                    for kind in (tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.DIRTYPE,
                                 tarfile.CHRTYPE, tarfile.BLKTYPE, tarfile.FIFOTYPE)]
        for entries in attacks:
            with self.subTest(entries=[(name, kind) for name, _content, kind in entries]):
                with self.assertRaises(ValueError):
                    vm.read_identity(io.BytesIO(identity_archive(entries=entries)))

    def test_vm_rejects_empty_or_oversized_identity_payloads(self):
        settings = {"ephemeral": True, "disableUpdate": True, "gitHubUrl": vm.REPOSITORY}
        for content in (b"", b"x" * 262145):
            with self.subTest(size=len(content)):
                archive = identity_archive(entries=[
                    (".runner", json.dumps(settings).encode(), tarfile.REGTYPE),
                    (".credentials", b"{}", tarfile.REGTYPE),
                    (".credentials_rsaparams", content, tarfile.REGTYPE),
                ])
                with self.assertRaises(ValueError):
                    vm.read_identity(io.BytesIO(archive))
        with self.assertRaises(ValueError):
            vm.read_identity(io.BytesIO(b"x" * (1024 * 1024 + 1)))


class IdentityLifecycleTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        root = Path(self.temporary.name)
        self.state = root / "proof" / "slot-1"
        self.registered = []
        self.started = []
        for target, value in (("STATE_ROOT", root), ("STATE", self.state), ("STOPPING", False)):
            patcher = patch.object(manage, target, value)
            patcher.start()
            self.addCleanup(patcher.stop)
        for target in ("ensure_proxy", "signal.signal", "time.sleep"):
            patcher = patch("manage." + target)
            patcher.start()
            self.addCleanup(patcher.stop)

    def register_identity(self):
        data = identity_archive({
            "agentId": len(self.registered) + 1,
            "ephemeral": True,
            "disableUpdate": True,
            "gitHubUrl": "https://github.com/GTimG/QuasiRiemannTracker",
        })
        self.registered.append(data)
        manage.private_write(self.state / "pending-identity.tar", data)

    def record_launch(self, args, **kwargs):
        if args[:len(manage.COMPOSE)] == manage.COMPOSE:
            self.assertFalse((self.state / "pending-identity.tar").exists())
            self.started.append(kwargs["input"])
            return True
        return False

    def test_every_completed_job_consumes_identity_and_registers_a_new_one(self):
        def execute(args, **kwargs):
            if self.record_launch(args, **kwargs) and len(self.started) == 2:
                manage.STOPPING = True
            return subprocess.CompletedProcess(args, 0)

        with patch.object(manage, "register", side_effect=self.register_identity):
            with patch.object(manage.subprocess, "run", side_effect=execute):
                manage.serve()
        self.assertEqual(self.started, self.registered)
        self.assertEqual(len(self.started), 2)
        self.assertNotEqual(*self.started)
        self.assertFalse((self.state / "pending-identity.tar").exists())

    def test_failed_job_identity_is_not_reused_after_supervisor_restart(self):
        def execute(args, **kwargs):
            if self.record_launch(args, **kwargs):
                if len(self.started) == 1:
                    return subprocess.CompletedProcess(args, 17)
                manage.STOPPING = True
            return subprocess.CompletedProcess(args, 0)

        with patch.object(manage, "register", side_effect=self.register_identity):
            with patch.object(manage.subprocess, "run", side_effect=execute):
                with self.assertRaises(RuntimeError):
                    manage.serve()
                self.assertFalse((self.state / "pending-identity.tar").exists())
                manage.serve()
        self.assertEqual(len(self.started), 2)
        self.assertNotEqual(*self.started)

    def test_interrupted_container_start_never_leaves_reusable_credentials(self):
        def execute(args, **kwargs):
            if self.record_launch(args, **kwargs):
                raise OSError("container startup interrupted")
            return subprocess.CompletedProcess(args, 0)

        with patch.object(manage, "register", side_effect=self.register_identity):
            with patch.object(manage.subprocess, "run", side_effect=execute):
                with self.assertRaises(OSError):
                    manage.serve()
        self.assertEqual(len(self.started), 1)
        self.assertFalse((self.state / "pending-identity.tar").exists())

    def test_watchdog_removes_timed_out_container_and_rotates_identity(self):
        events = []

        def execute(args, **kwargs):
            if self.record_launch(args, **kwargs):
                events.append("launch")
                if len(self.started) == 1:
                    raise subprocess.TimeoutExpired(args, manage.VM_LIFETIME_SECONDS)
                manage.STOPPING = True
            elif args == ["docker", "rm", "--force", "--volumes", manage.CONTAINER]:
                events.append("remove")
            return subprocess.CompletedProcess(args, 0)

        with patch.object(manage, "register", side_effect=self.register_identity):
            with patch.object(manage.subprocess, "run", side_effect=execute):
                manage.serve()
        self.assertEqual(len(self.started), 2)
        self.assertEqual(self.started, self.registered)
        self.assertNotEqual(*self.started)
        first_launch = events.index("launch")
        second_launch = events.index("launch", first_launch + 1)
        self.assertIn("remove", events[first_launch + 1:second_launch])
        self.assertFalse((self.state / "pending-identity.tar").exists())

    def test_registration_failure_cannot_fall_back_to_an_old_identity(self):
        with patch.object(manage, "register", side_effect=RuntimeError("registration unavailable")):
            with patch.object(manage.subprocess, "run") as execute:
                with self.assertRaises(RuntimeError):
                    manage.serve()
                execute.assert_not_called()
        self.assertFalse((self.state / "pending-identity.tar").exists())

    def test_shutdown_during_registration_does_not_launch_a_job(self):
        def register_then_stop():
            self.register_identity()
            manage.STOPPING = True

        def execute(args, **kwargs):
            self.record_launch(args, **kwargs)
            return subprocess.CompletedProcess(args, 0)

        with patch.object(manage, "register", side_effect=register_then_stop):
            with patch.object(manage.subprocess, "run", side_effect=execute):
                manage.serve()
        self.assertEqual(self.started, [])


class RegistrationIsolationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        self.state = root / "proof" / "slot-1"
        self.state.mkdir(parents=True)
        for target, value in (("STATE_ROOT", root), ("STATE", self.state)):
            patcher = patch.object(manage, target, value)
            patcher.start()
            self.addCleanup(patcher.stop)
        patcher = patch.object(manage, "registration_token", return_value="registration-token-test-secret")
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_registration_secret_is_only_sent_to_job_free_container_stdin(self):
        identity = identity_archive()
        calls = []

        def execute(args, **kwargs):
            calls.append((args, kwargs))
            return subprocess.CompletedProcess(args, 0, stdout=identity)

        with patch.object(manage.subprocess, "run", side_effect=execute):
            manage.register()
        registration = [(args, kwargs) for args, kwargs in calls if args[:len(manage.COMPOSE)] == manage.COMPOSE]
        self.assertEqual(len(registration), 1)
        args, options = registration[0]
        self.assertEqual(args[-2:], ["registration", "--register"])
        self.assertNotIn("registration-token-test-secret", str(args))
        self.assertNotIn("registration-token-test-secret", str(options.get("env", {})))
        self.assertEqual(options["input"], b"registration-token-test-secret\n")
        pending = self.state / "pending-identity.tar"
        self.assertEqual(pending.read_bytes(), identity)
        self.assertNotIn(b"registration-token-test-secret", pending.read_bytes())
        self.assertEqual(pending.stat().st_mode & 0o777, 0o600)

    def test_invalid_registration_output_is_never_published_for_jobs(self):
        data = identity_archive({
            "ephemeral": False,
            "disableUpdate": True,
            "gitHubUrl": "https://github.com/GTimG/QuasiRiemannTracker",
        })
        with patch.object(manage.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, stdout=data)):
            with self.assertRaises(RuntimeError):
                manage.register()
        self.assertFalse((self.state / "pending-identity.tar").exists())

    def test_registration_timeout_removes_container_and_publishes_no_identity(self):
        cleanup = []

        def execute(args, **kwargs):
            if args[:len(manage.COMPOSE)] == manage.COMPOSE:
                raise subprocess.TimeoutExpired(args, 120)
            cleanup.append(args)
            return subprocess.CompletedProcess(args, 0)

        with patch.object(manage.subprocess, "run", side_effect=execute):
            with self.assertRaises(subprocess.TimeoutExpired):
                manage.register()
        self.assertIn(["docker", "rm", "--force", "--volumes", manage.REGISTER], cleanup)
        self.assertFalse((self.state / "pending-identity.tar").exists())


class ProofServiceTests(unittest.TestCase):
    def test_install_retires_website_slots_before_enabling_proof_worker(self):
        with tempfile.TemporaryDirectory() as temporary:
            home = Path(temporary)
            units = home / ".config/systemd/user"
            units.mkdir(parents=True)
            for name in ("qrh-proof-runner.service", "qrh-actions-runner.service", "qrh-actions-runner@.service"):
                (units / name).write_text("legacy service")
            real_stat = manage.os.stat
            device_stat = real_stat(__file__)
            with patch.object(manage.Path, "home", return_value=home), patch.object(manage, "run") as execute:
                with patch.object(manage.os, "stat", side_effect=lambda path, *args, **kwargs:
                                  device_stat if path == "/dev/kvm" else real_stat(path, *args, **kwargs)):
                    manage.install_service()
            commands = [call.args[0] for call in execute.call_args_list]
            enable = ["systemctl", "--user", "enable", "qrh-proof-runner@1.service", "qrh-proof-runner@2.service"]
            for legacy in ("qrh-proof-runner.service", "qrh-actions-runner.service",
                           *[f"qrh-actions-runner@{slot}.service" for slot in (1, 2, 3)]):
                disable = ["systemctl", "--user", "disable", "--now", legacy]
                self.assertLess(commands.index(disable), commands.index(enable))
            unit = (units / manage.SERVICE).read_text()
            self.assertIn(f"QRH_KVM_GID={device_stat.st_gid}", unit)
            self.assertIn("serve --slot %i", unit)
            self.assertIn("docker rm --force --volumes qrh-proof-job-%i qrh-proof-register-%i", unit)

    def test_registration_token_is_shared_but_old_pending_identities_are_not_used(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            proof = root / "proof" / "slot-1"
            with patch.multiple(manage, STATE_ROOT=root, STATE=proof):
                manage.private_state()
                manage.private_write(root / "registration-token", b"fresh-host-token")
                manage.private_write(root / "pending-identity.tar", b"old-website-identity")
                with patch.object(manage.subprocess, "run", return_value=subprocess.CompletedProcess([], 1, stdout="")):
                    self.assertEqual(manage.registration_token(), "fresh-host-token")
                self.assertFalse((proof / "pending-identity.tar").exists())
                self.assertEqual(proof.stat().st_mode & 0o777, 0o700)


class SlotIsolationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        for target in ("STATE_ROOT", "STATE", "SLOT", "CONTAINER", "REGISTER"):
            patcher = patch.object(manage, target, getattr(manage, target))
            patcher.start()
            self.addCleanup(patcher.stop)
        manage.STATE_ROOT = self.root
        manage.select_slot(1)
        manage.private_state()

    def test_slots_can_run_together_but_not_twice_in_the_same_slot(self):
        with manage.slot_lock():
            manage.select_slot(2)
            manage.private_state()
            with manage.slot_lock():
                with self.assertRaises(BlockingIOError):
                    with manage.slot_lock():
                        self.fail("duplicate slot acquired its lock")
                manage.select_slot(1)
                with self.assertRaises(BlockingIOError):
                    with manage.slot_lock():
                        self.fail("duplicate first slot acquired its lock")
        with manage.slot_lock():
            pass

    def test_smoke_and_legacy_single_runner_exclude_both_slots(self):
        capacity = self.root / "proof" / "supervisor.lock"
        for slot in manage.SLOTS:
            manage.select_slot(slot)
            manage.private_state()
            with self.subTest(slot=slot):
                with manage.slot_lock():
                    with self.assertRaises(BlockingIOError):
                        with manage.file_lock(capacity, fcntl.LOCK_EX | fcntl.LOCK_NB):
                            self.fail("smoke ran alongside an active slot")
                with manage.file_lock(capacity, fcntl.LOCK_EX | fcntl.LOCK_NB):
                    with self.assertRaises(BlockingIOError):
                        with manage.slot_lock():
                            self.fail("slot ran during smoke or legacy verification")

    def test_registration_and_pending_identities_are_independent(self):
        old = self.root / "proof" / "pending-identity.tar"
        old.write_bytes(b"unused old single-service identity")
        calls = []
        paths = []
        identities = []

        def execute(args, **kwargs):
            calls.append(args)
            return subprocess.CompletedProcess(args, 0, stdout=identities[-1])

        with patch.object(manage, "registration_token", return_value="test-host-secret"):
            with patch.object(manage.subprocess, "run", side_effect=execute):
                for slot in manage.SLOTS:
                    manage.select_slot(slot)
                    manage.private_state()
                    identities.append(identity_archive({
                        "agentId": slot, "ephemeral": True, "disableUpdate": True,
                        "gitHubUrl": "https://github.com/GTimG/QuasiRiemannTracker",
                    }))
                    manage.register()
                    paths.append(manage.STATE / "pending-identity.tar")
        self.assertNotEqual(*paths)
        self.assertEqual([path.read_bytes() for path in paths], identities)
        self.assertEqual(old.read_bytes(), b"unused old single-service identity")
        registrations = [args for args in calls if args[:len(manage.COMPOSE)] == manage.COMPOSE]
        for slot, args in zip(manage.SLOTS, registrations):
            self.assertEqual(args[args.index("--name") + 1], f"qrh-proof-register-{slot}")
            name = next(arg for arg in args if arg.startswith("QRH_RUNNER_NAME="))
            self.assertRegex(name, rf"^QRH_RUNNER_NAME=qrh-proof-{slot}-[0-9a-f]{{12}}$")

    def test_slot_two_consumes_only_its_identity_and_stops_only_its_container(self):
        first_pending = manage.STATE / "pending-identity.tar"
        first_identity = identity_archive()
        manage.private_write(first_pending, first_identity)
        manage.select_slot(2)
        manage.private_state()
        second_pending = manage.STATE / "pending-identity.tar"
        second_identity = identity_archive({
            "agentId": 2, "ephemeral": True, "disableUpdate": True,
            "gitHubUrl": "https://github.com/GTimG/QuasiRiemannTracker",
        })
        manage.private_write(second_pending, second_identity)
        calls = []

        def execute(args, **kwargs):
            calls.append(args)
            if args[:len(manage.COMPOSE)] == manage.COMPOSE:
                self.assertEqual(args[args.index("--name") + 1], "qrh-proof-job-2")
                self.assertEqual(kwargs["input"], second_identity)
                self.assertFalse(second_pending.exists())
                manage.stop_job()
            return subprocess.CompletedProcess(args, 0)

        with patch.object(manage, "STOPPING", False), patch.object(manage, "ensure_proxy"):
            with patch.object(manage.signal, "signal"), patch.object(manage, "register") as register:
                with patch.object(manage.subprocess, "run", side_effect=execute):
                    manage.serve()
                register.assert_not_called()
        self.assertEqual(first_pending.read_bytes(), first_identity)
        self.assertFalse(second_pending.exists())
        self.assertIn(["docker", "stop", "--time", "20", "qrh-proof-job-2"], calls)
        self.assertFalse(any("qrh-proof-job-1" in args for args in calls))

    def test_proxy_creation_holds_shared_proxy_lock(self):
        def assert_locked():
            with self.assertRaises(BlockingIOError):
                with manage.file_lock(self.root / "proof" / "proxy.lock", fcntl.LOCK_EX | fcntl.LOCK_NB):
                    self.fail("proxy could be created concurrently")
        with patch.object(manage, "_ensure_proxy", side_effect=assert_locked) as create:
            manage.ensure_proxy()
            create.assert_called_once_with()

    def test_control_commands_address_both_slots_or_the_explicit_slot(self):
        real_stat = manage.os.stat
        device_stat = real_stat(__file__)
        for command in ("start", "stop", "status"):
            for slot in (None, 1, 2):
                argv = ["manage.py", command] + ([] if slot is None else ["--slot", str(slot)])
                with self.subTest(command=command, slot=slot):
                    with patch.object(manage.sys, "argv", argv), patch.object(manage, "run") as execute:
                        with patch.object(manage.os, "stat", side_effect=lambda path, *args, **kwargs:
                                          device_stat if path == "/dev/kvm" else real_stat(path, *args, **kwargs)):
                            manage.main()
                    services = manage.SERVICES if slot is None else (f"qrh-proof-runner@{slot}.service",)
                    expected = ["systemctl", "--user", command, *services]
                    if command == "status":
                        expected.append("--no-pager")
                    execute.assert_called_once_with(expected)

    def test_invalid_slots_and_slots_on_global_commands_are_rejected(self):
        for slot in (0, 3, -1, "1", True):
            with self.subTest(slot=slot):
                with self.assertRaises(ValueError):
                    manage.select_slot(slot)
        for arguments in (["serve", "--slot", "3"], ["register", "--slot", "0"],
                          ["smoke", "--slot", "1"], ["install-service", "--slot", "2"]):
            with self.subTest(arguments=arguments):
                with patch.object(manage.sys, "argv", ["manage.py", *arguments]):
                    with patch.object(manage.sys, "stderr", io.StringIO()), patch.object(manage, "private_state") as create:
                        with self.assertRaises(SystemExit) as raised:
                            manage.main()
                        self.assertEqual(raised.exception.code, 2)
                        create.assert_not_called()


if __name__ == "__main__":
    unittest.main()
