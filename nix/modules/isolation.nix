# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                    // foundry // modules/isolation
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# SCRAPER ISOLATION MODULE
#
# Three-layer trusted scraping stack:
#
#   Layer 3 (Strongest) - Firecracker microVMs
#     - Bare metal required (no nested virt)
#     - <125ms boot time, <5MB memory overhead
#     - Full hardware isolation via KVM
#     - Use for: High-value targets, untrusted content
#
#   Layer 2 (Default) - gVisor (runsc)
#     - Works on VMs (no bare metal required)
#     - Go-based application kernel
#     - Syscall interception + reimplementation
#     - Use for: External scraping, default isolation
#
#   Layer 1 (Fastest) - Container isolation
#     - Standard OCI containers with bubblewrap
#     - Fastest startup, lowest overhead
#     - Use for: Trusted domains, internal APIs
#
# ARCHITECTURE:
#   This module configures the NixOS host to support all three isolation levels.
#   The Haskell scraper runtime selects the appropriate level based on target
#   trust classification (see Foundry.Core.Scrape.Worker.IsolationLevel).
#
# DEPENDENCIES (from Haskell types):
#   - Foundry.Core.Scrape.Job:      ScrapeJob, IsolationLevel
#   - Foundry.Core.Scrape.Worker:   WorkerConfig (Container/GVisor/Firecracker)
#   - Foundry.Core.Scrape.Protocol: ZMQ messages for orchestration
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{
  config,
  lib,
  pkgs,
  ...
}:

let
  cfg = config.foundry.isolation;

  # ════════════════════════════════════════════════════════════════════════════════
  # TYPE DEFINITIONS
  # ════════════════════════════════════════════════════════════════════════════════

  isolationLevelType = lib.types.enum [
    "container"
    "gvisor"
    "firecracker"
  ];

  # Worker pool configuration (mirrors Haskell PoolConfig)
  poolConfigType = lib.types.submodule {
    options = {
      minWorkers = lib.mkOption {
        type = lib.types.ints.unsigned;
        default = 2;
        description = "Minimum number of workers to maintain (even when idle)";
      };

      maxWorkers = lib.mkOption {
        type = lib.types.ints.unsigned;
        default = 10;
        description = "Maximum number of concurrent workers";
      };

      idleTimeoutSeconds = lib.mkOption {
        type = lib.types.ints.unsigned;
        default = 300;
        description = "Seconds before idle workers are terminated";
      };

      healthCheckIntervalSeconds = lib.mkOption {
        type = lib.types.ints.unsigned;
        default = 30;
        description = "Interval between worker health checks";
      };

      maxJobsPerWorker = lib.mkOption {
        type = lib.types.ints.unsigned;
        default = 100;
        description = "Maximum jobs before worker is recycled";
      };
    };
  };

  # Firecracker VM configuration
  firecrackerConfigType = lib.types.submodule {
    options = {
      kernelPath = lib.mkOption {
        type = lib.types.path;
        description = "Path to vmlinux kernel image for Firecracker";
      };

      rootfsPath = lib.mkOption {
        type = lib.types.path;
        description = "Path to root filesystem image (ext4)";
      };

      vcpuCount = lib.mkOption {
        type = lib.types.ints.positive;
        default = 2;
        description = "Number of vCPUs per microVM";
      };

      memSizeMib = lib.mkOption {
        type = lib.types.ints.positive;
        default = 512;
        description = "Memory size in MiB per microVM";
      };

      networkInterface = lib.mkOption {
        type = lib.types.str;
        default = "eth0";
        description = "Network interface name inside microVM";
      };

      jailPath = lib.mkOption {
        type = lib.types.path;
        default = "/var/lib/foundry/firecracker/jail";
        description = "Chroot jail path for Firecracker instances";
      };
    };
  };

  # gVisor configuration
  gvisorConfigType = lib.types.submodule {
    options = {
      platform = lib.mkOption {
        type = lib.types.enum [
          "systrap"
          "kvm"
        ];
        default = "systrap";
        description = ''
          gVisor platform:
          - systrap: Pure userspace (works everywhere, slower)
          - kvm: Hardware acceleration (requires KVM, faster)
        '';
      };

      network = lib.mkOption {
        type = lib.types.enum [
          "sandbox"
          "host"
        ];
        default = "sandbox";
        description = ''
          Network mode:
          - sandbox: Isolated network stack (recommended for scraping)
          - host: Share host network (faster, less isolated)
        '';
      };

      fileAccess = lib.mkOption {
        type = lib.types.enum [
          "shared"
          "exclusive"
        ];
        default = "exclusive";
        description = ''
          File access mode:
          - exclusive: Better isolation, recommended
          - shared: Required for some workloads
        '';
      };

      overlay = lib.mkOption {
        type = lib.types.bool;
        default = true;
        description = "Use overlay filesystem for container rootfs";
      };

      debugLog = lib.mkOption {
        type = lib.types.bool;
        default = false;
        description = "Enable debug logging (reduces performance)";
      };
    };
  };

in
{
  # ════════════════════════════════════════════════════════════════════════════════
  # MODULE OPTIONS
  # ════════════════════════════════════════════════════════════════════════════════

  options.foundry.isolation = {
    enable = lib.mkEnableOption "Foundry scraper isolation stack";

    defaultLevel = lib.mkOption {
      type = isolationLevelType;
      default = "gvisor";
      description = ''
        Default isolation level for scrapers.
        Maps to Haskell IsolationLevel type.
      '';
    };

    # ──────────────────────────────────────────────────────────────────────────────
    # TALOS CONFIGURATION (Production VM management)
    # ──────────────────────────────────────────────────────────────────────────────

    talos = {
      enable = lib.mkEnableOption "Talos Linux management tooling";

      clusterEndpoint = lib.mkOption {
        type = lib.types.nullOr lib.types.str;
        default = null;
        example = "https://talos.cluster.local:6443";
        description = "Talos cluster API endpoint";
      };

      configDir = lib.mkOption {
        type = lib.types.path;
        default = "/etc/foundry/talos";
        description = "Directory for Talos configuration files";
      };
    };

    # ──────────────────────────────────────────────────────────────────────────────
    # GVISOR CONFIGURATION (Default scraper isolation)
    # ──────────────────────────────────────────────────────────────────────────────

    gvisor = {
      enable = lib.mkOption {
        type = lib.types.bool;
        default = true;
        description = "Enable gVisor (runsc) container runtime";
      };

      config = lib.mkOption {
        type = gvisorConfigType;
        default = { };
        description = "gVisor runtime configuration";
      };

      ociHandler = lib.mkOption {
        type = lib.types.str;
        default = "runsc";
        description = "OCI runtime handler name for gVisor";
      };
    };

    # ──────────────────────────────────────────────────────────────────────────────
    # FIRECRACKER CONFIGURATION (Strongest isolation)
    # ──────────────────────────────────────────────────────────────────────────────

    firecracker = {
      enable = lib.mkEnableOption "Firecracker microVM support";

      requireBareMetal = lib.mkOption {
        type = lib.types.bool;
        default = true;
        description = ''
          Require bare metal (no nested virtualization).
          Firecracker needs /dev/kvm access.
        '';
      };

      config = lib.mkOption {
        type = lib.types.nullOr firecrackerConfigType;
        default = null;
        description = "Firecracker microVM configuration";
      };
    };

    # ──────────────────────────────────────────────────────────────────────────────
    # WORKER POOL CONFIGURATION
    # ──────────────────────────────────────────────────────────────────────────────

    pool = lib.mkOption {
      type = poolConfigType;
      default = { };
      description = ''
        Worker pool configuration.
        Maps to Haskell PoolConfig type.
      '';
    };

    # ──────────────────────────────────────────────────────────────────────────────
    # NETWORK CONFIGURATION
    # ──────────────────────────────────────────────────────────────────────────────

    network = {
      bridgeName = lib.mkOption {
        type = lib.types.str;
        default = "foundry0";
        description = "Bridge interface for scraper network isolation";
      };

      subnet = lib.mkOption {
        type = lib.types.str;
        default = "10.200.0.0/16";
        description = "Subnet for scraper containers/VMs";
      };

      enableNAT = lib.mkOption {
        type = lib.types.bool;
        default = true;
        description = "Enable NAT for scraper outbound traffic";
      };
    };

    # ──────────────────────────────────────────────────────────────────────────────
    # STORAGE CONFIGURATION
    # ──────────────────────────────────────────────────────────────────────────────

    storage = {
      scratchDir = lib.mkOption {
        type = lib.types.path;
        default = "/var/lib/foundry/scratch";
        description = "Ephemeral storage for scraper workloads";
      };

      cacheDir = lib.mkOption {
        type = lib.types.path;
        default = "/var/cache/foundry";
        description = "Persistent cache for browser profiles, etc.";
      };

      maxScratchSizeGb = lib.mkOption {
        type = lib.types.ints.positive;
        default = 50;
        description = "Maximum scratch space in GB";
      };
    };

    # ──────────────────────────────────────────────────────────────────────────────
    # ZMQ ORCHESTRATION
    # ──────────────────────────────────────────────────────────────────────────────

    zmq = {
      backendEndpoint = lib.mkOption {
        type = lib.types.str;
        default = "tcp://127.0.0.1:5555";
        description = "ZMQ endpoint for backend orchestrator";
      };

      workerEndpoint = lib.mkOption {
        type = lib.types.str;
        default = "tcp://127.0.0.1:5556";
        description = "ZMQ endpoint for worker registration";
      };
    };
  };

  # ════════════════════════════════════════════════════════════════════════════════
  # MODULE IMPLEMENTATION
  # ════════════════════════════════════════════════════════════════════════════════

  config = lib.mkIf cfg.enable {

    # ──────────────────────────────────────────────────────────────────────────────
    # ASSERTIONS
    # ──────────────────────────────────────────────────────────────────────────────

    assertions = [
      {
        assertion = cfg.firecracker.enable -> cfg.firecracker.config != null;
        message = "foundry.isolation.firecracker.config must be set when Firecracker is enabled";
      }
      {
        assertion = cfg.pool.minWorkers <= cfg.pool.maxWorkers;
        message = "pool.minWorkers must be <= pool.maxWorkers";
      }
    ];

    # ──────────────────────────────────────────────────────────────────────────────
    # PACKAGES
    # ──────────────────────────────────────────────────────────────────────────────

    environment.systemPackages = lib.flatten [
      # Always include bubblewrap for basic sandboxing
      pkgs.bubblewrap

      # ZeroMQ for worker communication
      pkgs.zeromq

      # gVisor (runsc)
      (lib.optional cfg.gvisor.enable pkgs.gvisor)

      # Firecracker + firectl
      (lib.optionals cfg.firecracker.enable [
        pkgs.firecracker
        pkgs.firectl
      ])

      # Talos management
      (lib.optionals cfg.talos.enable [
        pkgs.talosctl
        pkgs.talhelper
      ])

      # Container tooling
      pkgs.podman
      pkgs.skopeo
      pkgs.umoci

      # Browser automation
      pkgs.playwright-driver
      pkgs.chromium
    ];

    # ──────────────────────────────────────────────────────────────────────────────
    # KERNEL MODULES
    # ──────────────────────────────────────────────────────────────────────────────

    boot.kernelModules = lib.flatten [
      # KVM for Firecracker (if enabled)
      (lib.optionals cfg.firecracker.enable [
        "kvm-intel"
        "kvm-amd"
      ])

      # TUN/TAP for network isolation
      [
        "tun"
        "tap"
        "veth"
        "bridge"
      ]
    ];

    # ──────────────────────────────────────────────────────────────────────────────
    # USER/GROUP
    # ──────────────────────────────────────────────────────────────────────────────

    users.groups.foundry-scraper = { };

    users.users.foundry-scraper = {
      isSystemUser = true;
      group = "foundry-scraper";
      description = "Foundry scraper worker user";
      home = "/var/lib/foundry";
      createHome = true;

      # Add to kvm group for Firecracker
      extraGroups = lib.optional cfg.firecracker.enable "kvm";
    };

    # ──────────────────────────────────────────────────────────────────────────────
    # DIRECTORIES
    # ──────────────────────────────────────────────────────────────────────────────

    systemd.tmpfiles.rules = [
      # Scratch directory (ephemeral, cleaned on boot)
      "d ${cfg.storage.scratchDir} 0750 foundry-scraper foundry-scraper -"
      "e ${cfg.storage.scratchDir} - - - 1d"

      # Cache directory (persistent)
      "d ${cfg.storage.cacheDir} 0750 foundry-scraper foundry-scraper -"

      # Talos config directory
      (lib.optionalString cfg.talos.enable "d ${cfg.talos.configDir} 0700 root root -")

      # Firecracker jail directory
      (lib.optionalString cfg.firecracker.enable "d ${cfg.firecracker.config.jailPath} 0700 foundry-scraper foundry-scraper -")
    ];

    # ──────────────────────────────────────────────────────────────────────────────
    # NETWORKING
    # ──────────────────────────────────────────────────────────────────────────────

    networking.bridges.${cfg.network.bridgeName} = {
      interfaces = [ ];
    };

    networking.interfaces.${cfg.network.bridgeName} = {
      ipv4.addresses = [
        {
          address =
            let
              parts = lib.splitString "/" cfg.network.subnet;
              network = builtins.head parts;
              networkParts = lib.splitString "." network;
            in
            "${builtins.elemAt networkParts 0}.${builtins.elemAt networkParts 1}.0.1";
          prefixLength = lib.toInt (builtins.elemAt (lib.splitString "/" cfg.network.subnet) 1);
        }
      ];
    };

    networking.nat = lib.mkIf cfg.network.enableNAT {
      enable = true;
      internalInterfaces = [ cfg.network.bridgeName ];
    };

    # ──────────────────────────────────────────────────────────────────────────────
    # PODMAN / OCI RUNTIME
    # ──────────────────────────────────────────────────────────────────────────────

    virtualisation.podman = {
      enable = true;

      # Enable rootless containers
      dockerCompat = false;

      # Add gVisor as an OCI runtime
      defaultNetwork.settings.dns_enabled = true;
    };

    # Configure gVisor as additional OCI runtime
    # This allows: podman run --runtime=runsc ...
    environment.etc."containers/containers.conf".text = lib.mkIf cfg.gvisor.enable ''
      [engine]
      runtime = "runc"

      [engine.runtimes]
      runsc = [
        "${pkgs.gvisor}/bin/runsc",
        "--platform=${cfg.gvisor.config.platform}",
        "--network=${cfg.gvisor.config.network}",
        "--file-access=${cfg.gvisor.config.fileAccess}",
        ${lib.optionalString cfg.gvisor.config.overlay ''
          "--overlay",
        ''}
        ${lib.optionalString cfg.gvisor.config.debugLog ''
          "--debug=true",
          "--debug-log=/var/log/foundry/runsc/",
        ''}
      ]
    '';

    # ──────────────────────────────────────────────────────────────────────────────
    # FIRECRACKER SETUP
    # ──────────────────────────────────────────────────────────────────────────────

    # Ensure /dev/kvm is accessible
    services.udev.extraRules = lib.mkIf cfg.firecracker.enable ''
      KERNEL=="kvm", GROUP="kvm", MODE="0660"
    '';

    # ──────────────────────────────────────────────────────────────────────────────
    # SYSTEMD SERVICES
    # ──────────────────────────────────────────────────────────────────────────────

    # Foundry scraper orchestrator service (placeholder)
    # The actual service will be defined when we have the Haskell binary
    systemd.services.foundry-scraper-orchestrator = {
      description = "Foundry Scraper Orchestrator";
      wantedBy = [ "multi-user.target" ];
      after = [ "network.target" ];

      serviceConfig = {
        Type = "notify";
        User = "foundry-scraper";
        Group = "foundry-scraper";
        Restart = "always";
        RestartSec = 5;

        # Security hardening
        NoNewPrivileges = true;
        ProtectSystem = "strict";
        ProtectHome = true;
        PrivateTmp = true;
        ProtectKernelTunables = true;
        ProtectKernelModules = true;
        ProtectControlGroups = true;
        RestrictAddressFamilies = [
          "AF_INET"
          "AF_INET6"
          "AF_UNIX"
        ];
        RestrictRealtime = true;
        RestrictSUIDSGID = true;
        MemoryDenyWriteExecute = true;
        LockPersonality = true;

        # Directories
        ReadWritePaths = [
          cfg.storage.scratchDir
          cfg.storage.cacheDir
        ];

        # Environment
        Environment = [
          "FOUNDRY_ZMQ_BACKEND=${cfg.zmq.backendEndpoint}"
          "FOUNDRY_ZMQ_WORKER=${cfg.zmq.workerEndpoint}"
          "FOUNDRY_ISOLATION_DEFAULT=${cfg.defaultLevel}"
          "FOUNDRY_POOL_MIN=${toString cfg.pool.minWorkers}"
          "FOUNDRY_POOL_MAX=${toString cfg.pool.maxWorkers}"
        ];
      };

      # Placeholder - will be replaced with actual binary path
      script = ''
        echo "Foundry scraper orchestrator starting..."
        echo "Backend endpoint: ${cfg.zmq.backendEndpoint}"
        echo "Worker endpoint: ${cfg.zmq.workerEndpoint}"
        echo "Default isolation: ${cfg.defaultLevel}"
        echo "Waiting for foundry-scraper binary to be built..."
        sleep infinity
      '';
    };
  };
}
